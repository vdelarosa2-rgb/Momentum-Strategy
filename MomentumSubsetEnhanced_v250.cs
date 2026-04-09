// Version: 2.51 - Per-Bar Regime Telemetry (Rolling Window Calibration Data)
#region Using declarations
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Windows;
using System.Windows.Input;
using System.Windows.Media;
using System.Xml.Serialization;
using NinjaTrader.Cbi;
using NinjaTrader.Gui;
using NinjaTrader.Gui.Chart;
using NinjaTrader.Gui.SuperDom;
using NinjaTrader.Gui.Tools;
using NinjaTrader.Data;
using NinjaTrader.NinjaScript;
using NinjaTrader.Core.FloatingPoint;
using NinjaTrader.NinjaScript.Indicators;
using NinjaTrader.NinjaScript.DrawingTools;
#endregion

namespace NinjaTrader.NinjaScript.Strategies
{
    #region Enums
    public enum ImbalanceEdgeHandlingMode
    {
        IgnoreEdgeLevels,
        HorizontalFallback,
        ZeroFallback
    }

    public enum MarketRegime
    {
        Flat,
        BullDiv,
        BearDiv,
        BullConv,
        BearConv
    }

    public enum VolatilityRegime
    {
        Init,
        Dead,
        Quiet,
        Normal,
        Active,
        Extreme
    }

    public enum SessionContext
    {
        SessionLowRev,
        LowerCont,
        MidRange,
        UpperCont,
        SessionHighBo
    }

    public enum SessionLocationBucket
    {
        Basement,
        Lower,
        Mid,
        Upper,
        Ceiling
    }

    public enum ValueAreaContext
    {
        NoVA,
        BelowVAL,
        AtVAL,
        InValue,
        AtPOC,
        AtVAH,
        AboveVAH
    }

    public enum DeltaMomentum
    {
        AccelBuy,
        DecelBuy,
        DecelSell,
        AccelSell,
        Neutral
    }

    public enum AvwapAnchorType
    {
        SessionOpen,
        SessionHigh,
        SessionLow
    }

    public enum AdaptiveContextFamily
    {
        Unknown,
        BasementValueReclaim,
        BelowValueReversal,
        WithGrainContinuation,
        MidRangeChop,
        UpperValueFriction,
        CeilingBreakout,
        LocationConflict,
        // Short-side families
        CeilingValueReject,
        AboveValueReversal,
        WithGrainShortContinuation,
        LowerValueFriction,
        BasementBreakdown
    }

    public enum MicrostructureRegime
    {
        Warmup,
        Dense,
        Normal,
        Thin
    }
    #endregion

    public class MomentumSubsetEnhanced : Strategy
    {
        #region Constants
        // Adaptive / Performance Gate Defaults
        private const double DefaultAdaptiveVolumeMinMultiplier = 0.60;
        private const double DefaultAdaptiveVolumeMaxStdDevMultiplier = 1.5;
        private const double DefaultTimeAdjustedVolumeMinMultiplier = 0.60;

        // Follow-Through Analysis Defaults
        private const double DefaultFollowThroughMinRate = 0.40;
        private const int DefaultFollowThroughMinSamples = 3;
        private const double DefaultFollowThroughMinTicks = 5.0;
        
        // Spread & Order Safety
        private const int SpreadCushionTicks = 4;
        
        // Session Position Thresholds (0.0 to 1.0 scale)
        private const double SessionPosLowRevThreshold = 0.20;
        private const double SessionPosLowerContThreshold = 0.40;
        private const double SessionPosMidRangeThreshold = 0.60;
        private const double SessionPosUpperContThreshold = 0.80;
        
        // Z-Score Thresholds for Volatility Regime
        private const double ZScoreDeadThreshold = -1.5;
        private const double ZScoreQuietThreshold = -0.5;
        private const double ZScoreActiveThreshold = 0.5;
        private const double ZScoreExtremeThreshold = 2.0;
        
        // Time-Based Volume Requirements
        private const int MinHourlySamplesForBaseline = 10;
        
        // Default Fallback Values
        private const double DefaultSessionPosition = 0.5;
        private const double DefaultStackRecency = 0.5;
        
        // Climax/Exhaustion Constants
        private const double ClimaxVolumeZScoreThreshold = 2.0;
        private const double ClimaxRangeRatioMax = 0.80;
        private const double ExhaustionVolumeDropRatio = 0.50;
        
        // Value Area Constants
        private const double ValueAreaPercentage = 0.70;
        private const int MinTicksForValueArea = 15;
        private const int ValueAreaPOCProximityTicks = 2;
        private const int ValueAreaEdgeProximityTicks = 2;
        
        // Delta Velocity Constants
        private const double DeltaROCNormalizationFactor = 50.0;
        private const double DeltaAccelNormalizationFactor = 30.0;
        private const double DeltaVelocityROCWeight = 0.6;
        private const double DeltaVelocityAccelWeight = 0.4;
        
        // NYSE Session Times (Eastern)
        private static readonly TimeSpan NYSEOpenTime = new TimeSpan(9, 30, 0);
        private static readonly TimeSpan NYSECloseTime = new TimeSpan(16, 0, 0);
        private static readonly TimeSpan PremarketStartTime = new TimeSpan(4, 0, 0);
        private static readonly TimeSpan PremarketEndTime = new TimeSpan(9, 29, 59);
        private static readonly TimeSpan InitialBalanceEndTime = new TimeSpan(10, 30, 0);
        #endregion

        #region Private Fields
        private DateTime lastExitTime = DateTime.MinValue;
        private DateTime _lastExecutionTime = DateTime.MinValue;
        private int lastTradeCount = 0;
        private bool hasPrintedSettings = false;

        private SessionIterator sessionIterator;
        private DateTime currentTradingDay = DateTime.MinValue;

        private bool breakEvenTriggered = false;
        private double highestSeenPrice = 0;
        private double lowestSeenPrice = 0;
        private double currentStopPrice = 0;
        private int lastTrailStep = -1;

        private double sessionStartProfit = 0.0;
        private bool dailyProfitHit = false;
        private bool shadowProfitHit = false;

        private string pendingTradeLog = "";

        // Lightweight rolling cache for POC Migration
        private double prevPoc1 = 0.0;
        private double prevPoc2 = 0.0;
        private int pocBarsProcessed = 0;
        #endregion

        #region Telemetry Infrastructure
        private double[] volumeBuffer;
        private double[] deltaBuffer;
        private int bufferIndex = 0;
        private bool adaptiveReady = false;
        private int adaptiveLookback = 50;
        private double adaptiveVolumeBaseline = 0;
        private double adaptiveVolumeStdDev = 0;
        private double adaptiveDeltaBaseline = 0;
        private double adaptiveDeltaStdDev = 0;

        private double sessionHigh = double.MinValue;
        private double sessionLow = double.MaxValue;
        private bool sessionInitialized = false;

        // Key Level Tracking (event-location branch)
        private double priorDayHigh = 0.0;
        private double priorDayLow = 0.0;
        private double premarketHigh = double.MinValue;
        private double premarketLow = double.MaxValue;
        private bool premarketInitialized = false;
        private double initialBalanceHigh = double.MinValue;
        private double initialBalanceLow = double.MaxValue;
        private bool initialBalanceLocked = false;

        // AVWAP Anchor & Acceptance Tracking
        private int rthOpenBarIdx = -1; 
        private int sessionHighBarIdx = -1;
        private int sessionLowBarIdx = -1;
        private bool hasReclaimedOpenVwap = false;
        private bool hasReclaimedHighVwap = false;
        private bool hasReclaimedLowVwap = false;

        private Queue<TradeResult> recentTradeResults = new Queue<TradeResult>();
        private int maxTradeMemory = 15;

        private Dictionary<int, List<double>> volumeByHour = new Dictionary<int, List<double>>();
        private int maxSamplesPerHour = 50;

        // Stack Clustering Memory
        private struct StackInfo
        {
            public int BarIndex;
            public double BottomPrice;
            public double TopPrice;
            public int Size;
        }
        private List<StackInfo> recentBullStacks = new List<StackInfo>();
        private List<StackInfo> recentBearStacks = new List<StackInfo>();
        private int maxStackMemory = 10;

        // Daily Summary Stats
        private int dailyTradeCount = 0;
        private int dailyWins = 0;
        private int dailyLosses = 0;
        private double dailyPnlTicks = 0;
        private Dictionary<string, int> dailyContextCounts = new Dictionary<string, int>();
        private Dictionary<string, double> dailyContextPnl = new Dictionary<string, double>();
        private Dictionary<string, int> dailyRegimeCounts = new Dictionary<string, int>();
        private Dictionary<string, double> dailyRegimePnl = new Dictionary<string, double>();

        // Dedicated Daily Cluster Tracking
        private Dictionary<string, int> dailyClusterCounts = new Dictionary<string, int>();
        private Dictionary<string, double> dailyClusterPnl = new Dictionary<string, double>();

        private struct TradeResult
        {
            public double MfeTicks;
            public double MaeTicks;
            public double PnlTicks;
            public string Context;
            public string VolRegime;
            public double StackRecency;
            public int ClusterCount;
            public DateTime EntryTime;
        }

        private struct AdaptiveRuleProfile
        {
            public bool DisableBarVolumeDependentFilters;
            public bool UseMinEscape;
            public double MinEscape;
            public bool UseMaxEscape;
            public double MaxEscape;
            public bool UseMinDomVol;
            public double MinDomVol;
            public bool UseMaxDomVol;
            public double MaxDomVol;
            public double MinRatio;
            public bool RequireImprovingDelta;
            public bool RequirePositiveBarDelta;
            public bool RequirePocLift;
            public bool RequireAvwapReclaim;
            public bool UseCeilingTrapKillSwitch;
            public double CeilingTrapAbsorptionPct;
        }

        // Entry-time telemetry snapshot
        private string lastEntryContext = "";
        private string lastEntryVolRegime = "";
        private double lastEntryStackRecency = 0;
        private double lastEntrySessionPos = 0;
        private double lastEntryVolZScore = 0;
        private double lastEntryAdaptiveMinVol = 0;
        private double lastEntryAdaptiveMaxVol = 0;
        private double lastEntryTimeBaseline = 0;
        private double lastEntryFollowThroughRate = 0;
        private double lastEntryAvgMfe = 0;
        private int lastEntryClusterCount = 0;

        // Adaptive & Perf Snapshots
        private double lastEntryAdaptiveVolBase = 0;
        private double lastEntryAdaptiveVolStdDev = 0;
        private double lastEntryTotalBarVol = 0;
        private double lastEntryVolumeSpikeRatio = 0;
        private double lastEntryTimeAdjMinVol = 0;
        private int lastEntryFtSampleCount = 0;
        private double lastEntryFtAvgMae = 0;
        private int lastEntryNetCnt = 0;
        private bool lastEntryRegimeAllowed = true;
        private bool lastEntryBaseStackPass = false;
        private bool lastEntryPreMatrixPass = false;
        private bool lastEntryMatrixVerdict = false;

        // Deep Footprint Snapshots
        private double lastEntryOlderSlope = 0;
        private double lastEntrySlopeAccel = 0;
        private double lastEntryBarDelta = 0;
        private double lastEntryNormDeltaPct = 0;
        private string lastEntryBarDir = "";
        private double lastEntryPrevBarDelta1 = 0;
        private double lastEntryPrevBarDelta2 = 0;
        private bool lastEntryImprovingDelta = false;
        private bool lastEntryDivLong = false;
        private double lastEntryAbsPct = 0;
        private double lastEntryAbsMult = 0;
        private double lastEntryLowZoneVol = 0;
        private double lastEntryLowBid = 0;
        private double lastEntryLowAsk = 0;
        private double lastEntryPocMig1 = 0;
        private bool lastEntryRevUp = false;
        private double lastEntryPrevPoc1 = 0;
        private double lastEntryPrevPoc2 = 0;
        private double lastEntryCurrentPoc = 0;

        // AVWAP Snapshots
        private double lastEntryAvwapOpen = 0;
        private double lastEntryAvwapHigh = 0;
        private double lastEntryAvwapLow = 0;
        private double lastEntryAvwapOpenHistorical = 0;
        private double lastEntryAvwapHighHistorical = 0;
        private double lastEntryAvwapLowHistorical = 0;
        private double lastEntryAvwapOpenSignalDistTicks = 0;
        private double lastEntryAvwapHighSignalDistTicks = 0;
        private double lastEntryAvwapLowSignalDistTicks = 0;
        private string lastEntryAvwapOpenTier = "";
        private string lastEntryAvwapHighTier = "";
        private string lastEntryAvwapLowTier = "";
        private string lastEntryAvwapOpenSlope = "";
        private string lastEntryAvwapHighSlope = "";
        private string lastEntryAvwapLowSlope = "";
        private double lastEntryAvwapOpenSlopeDropTicks = 0;
        private double lastEntryAvwapHighSlopeDropTicks = 0;
        private double lastEntryAvwapLowSlopeDropTicks = 0;
        private bool lastEntryAvwapOpenReclaimed = false;
        private bool lastEntryAvwapHighReclaimed = false;
        private bool lastEntryAvwapLowReclaimed = false;
        private string lastEntryAvwapTier = "";
        private string lastEntryAvwapSlope = "";
        private double lastEntryAvwapSlopeDropTicks = 0;
        private double lastEntryAvwapSignalDistTicks = 0;
        private string lastEntryAvwapActiveAnchor = "";
        private bool lastEntryAvwapReclaimed = false;

        private bool lastEntryPassCdAccel = true;
        private bool lastEntryPassDeltaDiv = true;
        private bool lastEntryPassAbsorb = true;
        private bool lastEntryPassPocMig = true;

        // Expanded Spatial / Liquidity / Matrix Telemetry
        private string lastEntryAdaptiveFamily = "";
        private string lastEntryAdaptiveRuleSummary = "";
        private string lastEntryMatrixProofState = "";
        private string lastEntryMatrixBlockReason = "";
        private bool lastEntryConstantVolumeMode = false;
        private bool lastEntryDisableBarVolumeFilters = false;
        private string lastEntrySessionAxis = "";
        private string lastEntrySpatialPair = "";

        // Spread & Book Depth telemetry
        private double lastEntrySignalSpread = 0.0;
        private double lastEntryAvgSpread = 0.0;
        private double lastEntryMaxSpread = 0.0;
        private double lastEntryBookBidVol = 0.0;
        private double lastEntryBookAskVol = 0.0;

        // Bar-level spread tracking
        private double barSpreadSum = 0;
        private double barSpreadMax = 0;
        private int barSpreadCount = 0;
        private double barSpreadMin = double.MaxValue;

        private double lastEntrySignalPrice = 0;
        private double lastEntrySessionHigh = 0;
        private double lastEntrySessionLow = 0;
        private double lastEntrySessionMid = 0;
        private double lastEntrySignalBarRangeTicks = 0;
        private double lastEntrySignalBarSecs = 0;
        private double lastEntryRangePer1kVolumeTicks = 0;
        private double lastEntryDeltaPerTick = 0;
        private double lastEntryDeltaPctOfVolume = 0;
        private double lastEntryImbalanceDensity = 0;
        private double lastEntryPocVolPct = 0;
        private double lastEntryMaxVolAtPrice = 0;
        private double lastEntryUpperZoneVol = 0;
        private double lastEntryUpperZonePct = 0;
        private double lastEntryLowZonePct = 0;
        private int lastEntryBullishImbalanceCount = 0;
        private int lastEntryBearishImbalanceCount = 0;
        private int lastEntryMaxBullishStack = 0;
        private int lastEntryMaxBearishStack = 0;
        private double lastEntryEscapeTicks = 0;
        private double lastEntryDomVolPercent = 0;
        private double lastEntryValidBullishRatio = 0;
        private double lastEntryPocPosition = 0;
        private bool lastEntryRangeBarMode = false;
        private string lastEntryRangePace = "";
        private double lastEntryRangeClosePos = 0;
        private double lastEntryRangeBodyPct = 0;
        private double lastEntryRangeOverlapPct = 0;
        private double lastEntryRangeLowerWickPct = 0;
        private double lastEntryRangeUpperWickPct = 0;
        private double lastEntryPriceToSessionLowTicks = 0;
        private double lastEntryPriceToSessionHighTicks = 0;
        private double lastEntryPriceToSessionMidTicks = 0;
        private double lastEntryPriceToVALTicks = 0;
        private double lastEntryPriceToVAHTicks = 0;
        private double lastEntryPriceToPOCSignedTicks = 0;
        private string lastEntryKeyLevelSummary = "";
        private string lastEntryNearestKeyLevel = "NONE";
        private double lastEntryNearestKeyLevelDistTicks = 0;
        private bool lastEntryNearVWAP = false;
        private bool lastEntryNearPDH = false;
        private bool lastEntryNearPDL = false;
        private bool lastEntryNearIBH = false;
        private bool lastEntryNearIBL = false;
        private bool lastEntryNearPMH = false;
        private bool lastEntryNearPML = false;
        private bool lastEntryNearPOC = false;
        private bool lastEntryKeyLevelGatePass = true;

        // Exit-management telemetry latched before trade-management state resets
        private bool lastClosedTradeBreakEvenTriggered = false;
        private bool lastClosedTradeTrailTriggered = false;
        private int lastClosedTradeMaxTrailStep = -1;
        private double lastClosedTradeFinalStopPrice = 0;
        private double lastClosedTradeHighestSeenPrice = 0;

        #endregion

        #region Climax/Exhaustion Tracking
        private double[] barRangeBuffer;
        private int barRangeBufferIndex = 0;
        private bool barRangeBufferReady = false;
        private double avgBarRange = 0;
        private double prevBarVolume = 0;
        private double prevBarRange = 0;
        private bool prevBarWasClimax = false;
        
        // Telemetry
        private bool lastEntryBarIsClimax = false;
        private bool lastEntryBarIsExhaustion = false;
        private bool lastEntryPrevBarWasClimax = false;
        private double lastEntryClimaxScore = 0;
        private double lastEntryExhaustionScore = 0;
        private double lastEntryClimaxPrevVol = 0;
        private double lastEntryClimaxCurVol = 0;
        private bool lastEntryPassClimaxFilter = true;
        private bool lastEntryPassExhaustionFilter = true;
        #endregion

        #region Value Area Tracking (NYSE Session)
        private Dictionary<int, double> nyseSessionVolumeByTick = new Dictionary<int, double>();
        private double nyseSessionTotalVolume = 0;
        private double nyseSessionVAH = 0;
        private double nyseSessionVAL = 0;
        private double nyseSessionPOC = 0;
        private bool nyseValueAreaValid = false;
        private DateTime lastNYSESessionDate = DateTime.MinValue;
        
        // Telemetry
        private double lastEntryVAH = 0;
        private double lastEntryVAL = 0;
        private double lastEntrySessionPOCVA = 0;
        private double lastEntryPriceDistToPOC = 0;
        private string lastEntryVAContext = "";
        private bool lastEntryPassVAFilter = true;
        #endregion

        #region Delta Velocity Tracking
        private double[] deltaVelocityHistory;
        private int deltaVelocityIndex = 0;
        private bool deltaVelocityReady = false;
        
        private double currentDeltaROC = 0;
        private double currentDeltaAccel = 0;
        private double deltaVelocityScore = 0;
        private DeltaMomentum currentDeltaMomentum = DeltaMomentum.Neutral;
        
        // Telemetry
        private double lastEntryDeltaROC = 0;
        private double lastEntryDeltaAccel = 0;
        private double lastEntryDeltaVelocityScore = 0;
        private string lastEntryDeltaMomentum = "";
        private bool lastEntryPassDeltaVelocityFilter = true;
        #endregion

        #region Volatility Regime Gate Telemetry
        private bool lastEntryVolRegimeGateAllowed = true;
        #endregion

        #region Session Context and Signal Quality Gate Telemetry
        private bool lastEntrySessionContextGateAllowed = true;
        private bool lastEntryMinSecsPass = true;
        private bool lastEntryMaxEscapeGlobalPass = true;
        private bool lastEntryAdaptive40RangeFilterPass = true;
        private bool lastEntryESRangeFilterPass = true;
        #endregion

        #region Microstructure Regime Tracking
        private Queue<double> r1kRollingBuffer = new Queue<double>();

        private double rollingR1k = 0.0;
        private MicrostructureRegime currentMicroRegime = MicrostructureRegime.Warmup;
        private double lastEntryRollingR1k = 0.0;
        private string lastEntryMicroRegime = "WARMUP";
        #endregion

        #region OnStateChange
        protected override void OnStateChange()
        {
            if (State == State.SetDefaults)
            {
                Description = "Institutional Imbalance Engine v2.53 (Tier 1 Revert)";
                Name = "MomentumSubsetEnhanced";
                Calculate = Calculate.OnPriceChange;
                EntriesPerDirection = 1;
                EntryHandling = EntryHandling.AllEntries;
                IsExitOnSessionCloseStrategy = false;
                ExitOnSessionCloseSeconds = 30;
                IsFillLimitOnTouch = false;
                MaximumBarsLookBack = MaximumBarsLookBack.TwoHundredFiftySix;
                OrderFillResolution = OrderFillResolution.Standard;
                StartBehavior = StartBehavior.WaitUntilFlat;
                TimeInForce = TimeInForce.Gtc;
                TraceOrders = false;
                RealtimeErrorHandling = RealtimeErrorHandling.StopCancelClose;
                StopTargetHandling = StopTargetHandling.PerEntryExecution;
                BarsRequiredToTrade = 40;

                AllowLongTrades = true;
                AllowShortTrades = false;

                AllowBullDiv = true;
                AllowBearDiv = true;
                AllowBullConv = true;
                AllowBearConv = true;

                UseCooldown = true;
                CooldownMinutes = 1;

                UseDiagonalImbalance = true;
                ImbalanceRatio = 1.0;
                MaxImbalanceRatio = 99.0;
                MinImbalanceVolume = 15;
                EdgeHandlingMode = ImbalanceEdgeHandlingMode.HorizontalFallback;
                AllowInfiniteEdgeRatio = false;

                ResetAdaptiveOnDayTransition = true;

                // Volatility Regime Gate
                UseVolatilityRegimeGate = false;
                AllowDeadRegime = false;
                AllowQuietRegime = true;
                AllowNormalRegime = true;
                AllowActiveRegime = true;
                AllowExtremeRegime = false;

                // Microstructure Regime Filter
                EnableRegimeFilter = false;
                R1kRollingWindowBars = 20;  // Default: 20 bars (good for 22-range); use 30 for 40-range bars
                RegimeDenseThreshold = 150.0;
                RegimeThinThreshold = 300.0;
                AllowDenseRegime = true;
                AllowNormalMicroRegime = true;
                AllowThinRegime = true;
                AllowWarmupRegime = false;

                // Climax/Exhaustion Filter
                UseClimaxFilter = false;
                BlockEntryOnClimaxBar = false;
                RequirePostClimaxEntry = false;
                UseExhaustionFilter = false;
                RequireExhaustionSetup = false;

                // Adaptive 40 Range Filter
                UseAdaptive40RangeFilter = false;
                Block_LowerCont_AccelBuy = true;
                Block_MidRange_AccelBuy = true;
                Block_NIC1 = true;

                // ES 8-Range Filter
                UseESRangeFilter = false;
                ES_Block_HighBO_AccelBuy = true;
                ES_Block_UpperFriction_Quiet_AccelBuy = true;
                ES_Block_AvwapExtreme = true;

                // Phase 1 Blocking Rules
                BlockSessLowRev = true;
                BlockCeilingActiveAboveVAH = true;

                // Week 2 Blocking Rules
                BlockLowerContBelowValLowVol = true;
                BlockCeilingAtVAH = true;
                BlockLowerContCluster2 = true;

                // Value Area Filter
                UseValueAreaFilter = false;
                VA_AllowNoVA = true;
                VA_AllowBelowVAL = true;
                VA_AllowAtVAL = true;
                VA_AllowInValue = true;
                VA_AllowAtPOC = true;
                VA_AllowAtVAH = true;
                VA_AllowAboveVAH = true;
                VA_RequirePOCTouch = false;
                VA_POCTouchLookbackBars = 5;

                // Delta Velocity Filter
                UseDeltaVelocityFilter = false;
                DeltaVelocityLookback = 5;
                DV_MinDeltaROC = 0;
                DV_RequirePositiveAccel = false;
                DV_BlockAcceleratingSelling = false;

                // Adaptive / Performance Gates
                UseAdaptiveVolumeGate = false;
                AdaptiveVolumeMinMultiplier = DefaultAdaptiveVolumeMinMultiplier;
                AdaptiveVolumeMaxStdDevMultiplier = DefaultAdaptiveVolumeMaxStdDevMultiplier;
                UseTimeAdjustedVolumeGate = false;
                TimeAdjustedVolumeMinMultiplier = DefaultTimeAdjustedVolumeMinMultiplier;
                UseFollowThroughGate = false;
                FollowThroughMinRate = DefaultFollowThroughMinRate;
                FollowThroughMinSamples = DefaultFollowThroughMinSamples;
                FollowThroughMinTicks = DefaultFollowThroughMinTicks;

                // ANCHORED VWAP FILTER (4-Tier Engine)
                UseAvwapFilter = false;
                AvwapAnchor = AvwapAnchorType.SessionOpen;
                AvwapDeadzoneTicks = 16;
                AvwapExtremeTicks = 60;
                AvwapKillzoneTicks = 90;
                UseAvwapSlopeFilter = true;
                AvwapSlopeLookbackBars = 10;
                AvwapSlopeVetoTicks = 4; // V2.28 Default for 12-Range NQ
                UseVwapAcceptanceFilter = true;

                // SESSION CONTEXT FILTER
                UseSessionContextFilter = false;
                Session_AllowLowRev = true;
                Session_AllowLowerCont = true;
                Session_AllowMidRange = true;
                Session_AllowUpperCont = true;
                Session_AllowHighBo = true;

                // SIGNAL QUALITY GLOBAL FILTERS
                UseMinBarSecs = false;
                MinBarSecsThreshold = 3.0;
                UseMaxEscapeGlobal = false;
                MaxEscapeGlobalTicks = 30.0;

                // ADAPTIVE CONTEXT MATRIX
                UseAdaptiveContextMatrix = false;
                AutoDisableBarVolumeFiltersOnConstantVolume = true;
                ShadowMatrixMode = false;
                AdaptiveBasementMinDomVol = 5.0;
                AdaptiveBasementMinEscape = -10.0;
                AdaptiveBasementRequireDeltaImprovement = true;
                AdaptiveContinuationMinDomVol = 4.5;
                AdaptiveCeilingMinDomVol = 10.0;
                AdaptiveCeilingMinRatio = 10.0;
                AdaptiveCeilingMinEscape = -10.0;
                AdaptiveCeilingMaxEscape = 20.0;
                AdaptiveCeilingTrapAbsorptionPct = 30.0;
                AdaptiveMidRangeMinDomVol = 8.0;
                AdaptiveMidRangeMinRatio = 5.0;
                AdaptiveMidRangeMinEscape = -10.0;
                AdaptiveMidRangeMaxEscape = 20.0;

                // RANGE BAR ADAPTATION
                UseRangeBarAdaptation = false;
                RangeFastBarSecsThreshold = 25.0;
                RangeSlowBarSecsThreshold = 90.0;
                RangeContinuationCloseMinPct = 0.70;
                RangeStrongSlowBarCloseMinPct = 0.80;
                RangeMaxOverlapPct = 0.70;
                RangeMinRejectionWickPct = 0.20;

                // TIER A PROFILE
                S3_Enable = true;
                S3_MinStackSize = 3;
                S3_MaxStackSize = 3;

                // Bull Count Filter
                S3_UseBullCount = false;
                S3_MinBullCount = 4;
                S3_MaxBullCount = 7;

                S3_UseCdSlope = true;
                S3_MinCdSlope = -15.0;
                S3_MaxCdSlope = 0.0;
                S3_CdLookback = 5;
                S3_RequireDivergence = true;
                S3_UseMinVolume = true;
                S3_MinVolume = 150;
                S3_UseMaxVolume = true;
                S3_MaxVolume = 400;
                S3_UseMaxImbVol = true;
                S3_MaxImbVol = 18.0;
                S3_UseDominance = true;
                S3_MinDomCount = 1;
                S3_MinDomDelta = 20.0;
                
                S3_UseVolumeSpike = false;
                S3_VolumeSpikeLookback = 5;
                S3_MinVolumeSpikeRatio = 1.3;
                S3_MaxVolumeSpikeRatio = 3.0;

                S3_UseMinPoc = false;
                S3_MinPoc = 0.0;
                S3_UsePoc = true;
                S3_MaxPoc = 0.35;
                
                S3_UseMinEscape = true;
                S3_MinEscape = 1;
                S3_UseMaxEscape = true;
                S3_MaxEscape = 4;
                S3_UseMinDomVol = true;
                S3_MinDomVol = 22.0;
                S3_UseMaxDomVol = true;
                S3_MaxDomVol = 30.0;
                
                // Bar Quality & Delta
                S3_UseBarDelta = false;
                S3_MinBarDelta = -200.0;
                S3_MaxBarDelta = 0.0;
                S3_UseNormalizedDelta = false;
                S3_MinNormalizedDeltaPct = 5.0;
                S3_MaxNormalizedDeltaPct = 100.0;

                S3_UseMinOppStack = false;
                S3_MinOppStack = 0;
                S3_UseMaxOppStack = false;
                S3_MaxOppStack = 2;

                S3_UseDeltaDivergence = false;
                S3_RequireDeceleration = false;
                S3_UseCdSlopeAccel = false;
                S3_MinCdSlopeAccel = 0.0;
                S3_CdSlopeAccelShift = 3;
                
                // Absorption
                S3_UseAbsorption = false;
                S3_MinAbsorptionPct = 0.0;
                S3_UseMaxAbsorption = false;
                S3_MaxAbsorptionPct = 39.9;
                S3_AbsorptionZoneTicks = 3;
                S3_MinAbsorptionMultiple = 1.5;
                
                S3_UsePocMigration = false;
                S3_RequirePocReversal = false;
                S3_MinPocMigrationTicks = 0;

                S3_UseRecency = false;
                S3_MinRecency = 0.30;
                S3_MaxRecency = 0.75;

                StopLossTicks = 30;
                TakeProfitTicks = 70;
                UseBreakEven = false;
                BreakEvenTriggerTicks = 40;
                BreakEvenOffsetTicks = 4;
                UseAutoTrail = false;
                AutoTrailTriggerTicks = 50;
                AutoTrailStopLossTicks = 25;
                AutoTrailFrequencyTicks = 1;
                UseMaxDailyProfit = false;
                MaxDailyProfit = 600.0;
                
                UseShadowDailyProfitTracker = false;
                ShadowDailyProfitTarget = 600.0;

                UseSessionFilter = true;
                SessionStart = DateTime.Parse("10:10", System.Globalization.CultureInfo.InvariantCulture);
                SessionEnd = DateTime.Parse("11:58", System.Globalization.CultureInfo.InvariantCulture);

                UseTradeLogging = true;

                // KEY LEVEL TELEMETRY / GATE
                UseKeyLevelGate = false;
                KeyLevelProximityTicks = 12;
                KL_AllowVWAP = true;
                KL_AllowPDH = true;
                KL_AllowPDL = true;
                KL_AllowIBH = true;
                KL_AllowIBL = true;
                KL_AllowPMH = true;
                KL_AllowPML = true;
                KL_AllowPOC = true;
                KL_RequireDeltaAgreement = false;
                KL_RequireAbsorptionForReversal = false;
                KL_AvoidMiddayChop = false;
                KL_MiddayStart = DateTime.Parse("12:00", System.Globalization.CultureInfo.InvariantCulture);
                KL_MiddayEnd = DateTime.Parse("14:00", System.Globalization.CultureInfo.InvariantCulture);
            }
            else if (State == State.DataLoaded)
            {
                sessionIterator = new SessionIterator(Bars);

                ResetAllState();

                volumeBuffer = new double[adaptiveLookback];
                deltaBuffer = new double[adaptiveLookback];
                barRangeBuffer = new double[adaptiveLookback];
                recentTradeResults = new Queue<TradeResult>();
                volumeByHour = new Dictionary<int, List<double>>();
                recentBullStacks = new List<StackInfo>();

                // Initialize Delta Velocity buffer
                deltaVelocityHistory = new double[DeltaVelocityLookback + 2];

                // Initialize Value Area tracking
                nyseSessionVolumeByTick = new Dictionary<int, double>();

                ResetDailyStats();

                SetStopLoss(CalculationMode.Ticks, StopLossTicks);
                SetProfitTarget(CalculationMode.Ticks, TakeProfitTicks);
            }
            else if (State == State.Terminated)
            {
                if (currentTradingDay != DateTime.MinValue && dailyTradeCount > 0)
                {
                    PrintDailySummary();
                }
            }
        }
        #endregion

        #region Helper Methods - State Management
        private void ResetAllState()
        {
            ResetTradeManagementState();
            dailyProfitHit = false;
            shadowProfitHit = false;
            currentTradingDay = DateTime.MinValue;
            lastExitTime = DateTime.MinValue;
            _lastExecutionTime = DateTime.MinValue;
            currentStopPrice = 0;
            lastTradeCount = 0;
            pendingTradeLog = "";
            hasPrintedSettings = false;

            prevPoc1 = 0.0;
            prevPoc2 = 0.0;
            pocBarsProcessed = 0;

            sessionHigh = double.MinValue;
            sessionLow = double.MaxValue;
            sessionInitialized = false;

            rthOpenBarIdx = -1;
            sessionHighBarIdx = -1;
            sessionLowBarIdx = -1;
            hasReclaimedOpenVwap = false;
            hasReclaimedHighVwap = false;
            hasReclaimedLowVwap = false;
            lastEntryAvwapActiveAnchor = "";
            lastEntryAvwapSlopeDropTicks = 0;
            lastEntryAvwapSignalDistTicks = 0;

            lastClosedTradeBreakEvenTriggered = false;
            lastClosedTradeTrailTriggered = false;
            lastClosedTradeMaxTrailStep = -1;
            lastClosedTradeFinalStopPrice = 0;
            lastClosedTradeHighestSeenPrice = 0;

            // Reset climax tracking
            prevBarVolume = 0;
            prevBarRange = 0;
            prevBarWasClimax = false;
            barRangeBufferIndex = 0;
            barRangeBufferReady = false;

            // Reset delta velocity
            deltaVelocityIndex = 0;
            deltaVelocityReady = false;
            currentDeltaROC = 0;
            currentDeltaAccel = 0;
            deltaVelocityScore = 0;

            // Reset value area
            ResetNYSEValueArea();
            ResetKeyLevelTracking();
        }

        private void ResetTradeManagementState()
        {
            breakEvenTriggered = false;
            highestSeenPrice = 0;
            lowestSeenPrice = 0;
            currentStopPrice = 0;
            lastTrailStep = -1;
        }

        private void ResetSessionTracking()
        {
            sessionHigh = double.MinValue;
            sessionLow = double.MaxValue;
            sessionInitialized = false;

            rthOpenBarIdx = -1;
            sessionHighBarIdx = -1;
            sessionLowBarIdx = -1;
            hasReclaimedOpenVwap = false;
            hasReclaimedHighVwap = false;
            hasReclaimedLowVwap = false;

            if (recentBullStacks != null)
                recentBullStacks.Clear();

            if (recentBearStacks != null)
                recentBearStacks.Clear();

            prevPoc1 = 0.0;
            prevPoc2 = 0.0;
            pocBarsProcessed = 0;

            premarketHigh = double.MinValue;
            premarketLow = double.MaxValue;
            premarketInitialized = false;
            initialBalanceHigh = double.MinValue;
            initialBalanceLow = double.MaxValue;
            initialBalanceLocked = false;

            if (r1kRollingBuffer != null)
                r1kRollingBuffer.Clear();
            rollingR1k = 0.0;
            currentMicroRegime = MicrostructureRegime.Warmup;
        }

        private void ResetAdaptiveBuffers()
        {
            bufferIndex = 0;
            barRangeBufferIndex = 0;
            adaptiveReady = false;
            barRangeBufferReady = false;
            if (volumeBuffer != null) Array.Clear(volumeBuffer, 0, volumeBuffer.Length);
            if (deltaBuffer != null) Array.Clear(deltaBuffer, 0, deltaBuffer.Length);
            if (barRangeBuffer != null) Array.Clear(barRangeBuffer, 0, barRangeBuffer.Length);
            if (volumeByHour != null) volumeByHour.Clear();
            if (recentTradeResults != null) recentTradeResults.Clear();
            
            adaptiveVolumeBaseline = 0;
            adaptiveVolumeStdDev = 0;
            adaptiveDeltaBaseline = 0;
            adaptiveDeltaStdDev = 0;
            avgBarRange = 0;
        }

        private void ResetDailyStats()
        {
            dailyTradeCount = 0;
            dailyWins = 0;
            dailyLosses = 0;
            dailyPnlTicks = 0;
            dailyContextCounts.Clear();
            dailyContextPnl.Clear();
            dailyRegimeCounts.Clear();
            dailyRegimePnl.Clear();
            dailyClusterCounts.Clear();
            dailyClusterPnl.Clear();
        }

        private void ResetNYSEValueArea()
        {
            if (nyseSessionVolumeByTick != null)
                nyseSessionVolumeByTick.Clear();
            nyseSessionTotalVolume = 0;
            nyseSessionVAH = 0;
            nyseSessionVAL = 0;
            nyseSessionPOC = 0;
            nyseValueAreaValid = false;
        }

        private double GetSignedTicksToReference(double price, double referencePrice)
        {
            if (referencePrice <= 0)
                return 0;

            return (price - referencePrice) / TickSize;
        }

        private string FormatSignedTicks(double ticks)
        {
            return string.Format("{0}{1:F1}T", ticks >= 0 ? "+" : "", ticks);
        }

        private SessionLocationBucket GetSessionLocationBucket(double sessionPos)
        {
            if (sessionPos <= SessionPosLowRevThreshold) return SessionLocationBucket.Basement;
            if (sessionPos <= SessionPosLowerContThreshold) return SessionLocationBucket.Lower;
            if (sessionPos <= SessionPosMidRangeThreshold) return SessionLocationBucket.Mid;
            if (sessionPos <= SessionPosUpperContThreshold) return SessionLocationBucket.Upper;
            return SessionLocationBucket.Ceiling;
        }

        private string GetSessionLocationBucketString(SessionLocationBucket bucket)
        {
            switch (bucket)
            {
                case SessionLocationBucket.Basement: return "BASEMENT";
                case SessionLocationBucket.Lower: return "LOWER";
                case SessionLocationBucket.Mid: return "MID";
                case SessionLocationBucket.Upper: return "UPPER";
                case SessionLocationBucket.Ceiling: return "CEILING";
                default: return "UNKNOWN";
            }
        }

        private bool IsCheapValueAreaContext(ValueAreaContext context)
        {
            return context == ValueAreaContext.BelowVAL || context == ValueAreaContext.AtVAL;
        }

        private bool IsNeutralValueAreaContext(ValueAreaContext context)
        {
            return context == ValueAreaContext.NoVA || context == ValueAreaContext.InValue || context == ValueAreaContext.AtPOC;
        }

        private bool IsRichValueAreaContext(ValueAreaContext context)
        {
            return context == ValueAreaContext.AtVAH || context == ValueAreaContext.AboveVAH;
        }

        private string GetSpatialPairLabel(SessionLocationBucket sessionBucket, ValueAreaContext vaContext)
        {
            return GetSessionLocationBucketString(sessionBucket) + "|" + GetValueAreaContextString(vaContext);
        }

        private string GetLocationBucketLabel(double sessionPos)
        {
            return GetSessionLocationBucketString(GetSessionLocationBucket(sessionPos));
        }
        #endregion

        #region Helper Methods - Telemetry
        private void UpdateAdaptiveBaselines(NinjaTrader.NinjaScript.BarsTypes.VolumetricBarsType vBarsType)
        {
            if (CurrentBar < 3) return;

            var baselineBar = vBarsType.Volumes[CurrentBar - 2];
            double barVolume = baselineBar.TotalVolume;
            double barDeltaVal = Math.Abs(baselineBar.BarDelta);
            double barRange = High[2] - Low[2];

            volumeBuffer[bufferIndex] = barVolume;
            deltaBuffer[bufferIndex] = barDeltaVal;
            barRangeBuffer[barRangeBufferIndex] = barRange;

            bufferIndex = (bufferIndex + 1) % adaptiveLookback;
            barRangeBufferIndex = (barRangeBufferIndex + 1) % adaptiveLookback;

            int hour = Time[2].Hour;
            List<double> hourlyVolumes;
            if (!volumeByHour.TryGetValue(hour, out hourlyVolumes))
            {
                hourlyVolumes = new List<double>();
                volumeByHour[hour] = hourlyVolumes;
            }
            hourlyVolumes.Add(barVolume);
            if (hourlyVolumes.Count > maxSamplesPerHour)
                hourlyVolumes.RemoveAt(0);

            if (CurrentBar >= adaptiveLookback)
            {
                adaptiveReady = true;
                barRangeBufferReady = true;

                double volSum = 0;
                double deltaSum = 0;
                double rangeSum = 0;
                for (int i = 0; i < adaptiveLookback; i++)
                {
                    volSum += volumeBuffer[i];
                    deltaSum += deltaBuffer[i];
                    rangeSum += barRangeBuffer[i];
                }
                adaptiveVolumeBaseline = volSum / adaptiveLookback;
                adaptiveDeltaBaseline = deltaSum / adaptiveLookback;
                avgBarRange = rangeSum / adaptiveLookback;

                double sumSqVol = 0;
                double sumSqDelta = 0;
                for (int i = 0; i < adaptiveLookback; i++)
                {
                    double volDiff = volumeBuffer[i] - adaptiveVolumeBaseline;
                    double deltaDiff = deltaBuffer[i] - adaptiveDeltaBaseline;
                    sumSqVol += volDiff * volDiff;
                    sumSqDelta += deltaDiff * deltaDiff;
                }
                adaptiveVolumeStdDev = Math.Sqrt(sumSqVol / adaptiveLookback);
                adaptiveDeltaStdDev = Math.Sqrt(sumSqDelta / adaptiveLookback);
            }
        }

        private void UpdateSessionTrackingConfirmedBar()
        {
            if (CurrentBar < 1)
                return;

            DateTime confirmedTime = Time[1];
            if (!IsWithinNYSESession(confirmedTime))
                return;

            int confirmedBarIndex = CurrentBar - 1;
            double confirmedHigh = High[1];
            double confirmedLow = Low[1];

            if (rthOpenBarIdx == -1 && confirmedTime.TimeOfDay >= NYSEOpenTime)
            {
                rthOpenBarIdx = confirmedBarIndex;
                hasReclaimedOpenVwap = false;
            }

            if (!sessionInitialized)
            {
                sessionInitialized = true;
                sessionHigh = confirmedHigh;
                sessionLow = confirmedLow;
                sessionHighBarIdx = confirmedBarIndex;
                sessionLowBarIdx = confirmedBarIndex;
                hasReclaimedHighVwap = false;
                hasReclaimedLowVwap = false;
            }
            else
            {
                if (confirmedHigh > sessionHigh)
                {
                    sessionHigh = confirmedHigh;
                    sessionHighBarIdx = confirmedBarIndex;
                    hasReclaimedHighVwap = false;
                }
                if (confirmedLow < sessionLow)
                {
                    sessionLow = confirmedLow;
                    sessionLowBarIdx = confirmedBarIndex;
                    hasReclaimedLowVwap = false;
                }
            }
        }

        private double CalculateAVWAP(NinjaTrader.NinjaScript.BarsTypes.VolumetricBarsType vBarsType, int anchorBarIndex, int shiftBars)
        {
            if (vBarsType == null) return 0;
            if (shiftBars < 0) return 0;
            if (anchorBarIndex < 0 || anchorBarIndex > CurrentBar - shiftBars) return 0;

            double cumVolPrice = 0;
            double cumVol = 0;

            int endBarIndex = CurrentBar - shiftBars;
            for (int i = anchorBarIndex; i <= endBarIndex; i++)
            {
                int barsAgo = CurrentBar - i;
                double typicalPrice = (High[barsAgo] + Low[barsAgo] + Close[barsAgo]) / 3.0;
                double vol = vBarsType.Volumes[i].TotalVolume;

                cumVolPrice += typicalPrice * vol;
                cumVol += vol;
            }

            return cumVol > 0 ? cumVolPrice / cumVol : 0;
        }


        private bool UpdateAnchorReclaimState(NinjaTrader.NinjaScript.BarsTypes.VolumetricBarsType vBarsType, int anchorBarIndex, bool alreadyReclaimed)
        {
            if (alreadyReclaimed) return true;
            if (anchorBarIndex < 0 || anchorBarIndex > CurrentBar - 1) return false;
            if (CurrentBar < 1) return false;

            double trackingVwap = CalculateAVWAP(vBarsType, anchorBarIndex, 1);
            if (trackingVwap <= 0) return false;

            return High[1] >= trackingVwap;
        }

        private double GetAnchorHistoricalAVWAP(NinjaTrader.NinjaScript.BarsTypes.VolumetricBarsType vBarsType, int anchorBarIndex)
        {
            if (anchorBarIndex < 0) return 0;

            int shift = 1 + Math.Min(AvwapSlopeLookbackBars, CurrentBar - anchorBarIndex);
            return CalculateAVWAP(vBarsType, anchorBarIndex, shift);
        }

        private string GetAvwapZoneLabel(double signalDistTicksBelow)
        {
            if (signalDistTicksBelow < AvwapDeadzoneTicks) return "DEADZONE/ABOVE";
            if (signalDistTicksBelow > AvwapKillzoneTicks) return "KILLZONE";
            if (signalDistTicksBelow > AvwapExtremeTicks) return "EXTREME";
            return "SWEETSPOT";
        }

        private string GetAvwapSlopeLabel(double slopeDropTicks)
        {
            return slopeDropTicks >= AvwapSlopeVetoTicks ? "FALLING" : "RISING/FLAT";
        }

        private void CaptureAnchorAvwapTelemetry(
            NinjaTrader.NinjaScript.BarsTypes.VolumetricBarsType vBarsType,
            int anchorBarIndex,
            bool reclaimedState,
            out double liveAvwap,
            out double historicalAvwap,
            out double signalDistTicksBelow,
            out double slopeDropTicks,
            out string zoneLabel,
            out string slopeLabel,
            out bool reclaimedOut)
        {
            liveAvwap = 0;
            historicalAvwap = 0;
            signalDistTicksBelow = 0;
            slopeDropTicks = 0;
            zoneLabel = "N/A";
            slopeLabel = "N/A";
            reclaimedOut = reclaimedState;

            if (anchorBarIndex < 0 || anchorBarIndex > CurrentBar - 1)
                return;

            liveAvwap = CalculateAVWAP(vBarsType, anchorBarIndex, 1);
            if (liveAvwap <= 0)
                return;

            historicalAvwap = GetAnchorHistoricalAVWAP(vBarsType, anchorBarIndex);
            signalDistTicksBelow = (liveAvwap - Close[1]) / TickSize;
            slopeDropTicks = historicalAvwap > 0 ? (historicalAvwap - liveAvwap) / TickSize : 0;

            zoneLabel = GetAvwapZoneLabel(signalDistTicksBelow);
            slopeLabel = GetAvwapSlopeLabel(slopeDropTicks);
        }

        private bool GetActiveAnchorReclaimState()
        {
            switch (AvwapAnchor)
            {
                case AvwapAnchorType.SessionOpen: return hasReclaimedOpenVwap;
                case AvwapAnchorType.SessionHigh: return hasReclaimedHighVwap;
                case AvwapAnchorType.SessionLow:  return hasReclaimedLowVwap;
                default: return false;
            }
        }

        private double GetZScore(double value, double baseline, double stdDev)
        {
            if (stdDev <= 0) return 0;
            return (value - baseline) / stdDev;
        }

        private VolatilityRegime GetVolatilityRegime(double currentVolume)
        {
            if (!adaptiveReady) return VolatilityRegime.Init;

            double zScore = GetZScore(currentVolume, adaptiveVolumeBaseline, adaptiveVolumeStdDev);

            if (zScore < ZScoreDeadThreshold) return VolatilityRegime.Dead;
            if (zScore < ZScoreQuietThreshold) return VolatilityRegime.Quiet;
            if (zScore > ZScoreExtremeThreshold) return VolatilityRegime.Extreme;
            if (zScore > ZScoreActiveThreshold) return VolatilityRegime.Active;
            return VolatilityRegime.Normal;
        }

        private string GetVolatilityRegimeString(VolatilityRegime regime)
        {
            switch (regime)
            {
                case VolatilityRegime.Init: return "INIT";
                case VolatilityRegime.Dead: return "DEAD";
                case VolatilityRegime.Quiet: return "QUIET";
                case VolatilityRegime.Normal: return "NORMAL";
                case VolatilityRegime.Active: return "ACTIVE";
                case VolatilityRegime.Extreme: return "EXTREME";
                default: return "UNKNOWN";
            }
        }

        private bool IsVolatilityRegimeAllowed(VolatilityRegime regime)
        {
            if (!UseVolatilityRegimeGate) return true;
            
            switch (regime)
            {
                case VolatilityRegime.Dead: return AllowDeadRegime;
                case VolatilityRegime.Quiet: return AllowQuietRegime;
                case VolatilityRegime.Normal: return AllowNormalRegime;
                case VolatilityRegime.Active: return AllowActiveRegime;
                case VolatilityRegime.Extreme: return AllowExtremeRegime;
                case VolatilityRegime.Init: return false; 
                default: return true;
            }
        }

        private bool IsSessionContextAllowed(SessionContext context)
        {
            if (!UseSessionContextFilter) return true;
            switch (context)
            {
                case SessionContext.SessionLowRev:  return Session_AllowLowRev;
                case SessionContext.LowerCont:      return Session_AllowLowerCont;
                case SessionContext.MidRange:       return Session_AllowMidRange;
                case SessionContext.UpperCont:      return Session_AllowUpperCont;
                case SessionContext.SessionHighBo:  return Session_AllowHighBo;
                default: return true;
            }
        }

        private double GetSessionPosition(double price)
        {
            if (!sessionInitialized || sessionHigh <= sessionLow)
                return DefaultSessionPosition;
            
            double range = sessionHigh - sessionLow;
            if (range < TickSize) return DefaultSessionPosition;
            
            return (price - sessionLow) / range;
        }

        private SessionContext GetStackContext(double sessionPosition)
        {
            if (sessionPosition <= SessionPosLowRevThreshold) return SessionContext.SessionLowRev;
            if (sessionPosition <= SessionPosLowerContThreshold) return SessionContext.LowerCont;
            if (sessionPosition <= SessionPosMidRangeThreshold) return SessionContext.MidRange;
            if (sessionPosition <= SessionPosUpperContThreshold) return SessionContext.UpperCont;
            return SessionContext.SessionHighBo;
        }

        private string GetSessionContextString(SessionContext context)
        {
            switch (context)
            {
                case SessionContext.SessionLowRev: return "SESS-LOW-REV";
                case SessionContext.LowerCont: return "LOWER-CONT";
                case SessionContext.MidRange: return "MID-RANGE";
                case SessionContext.UpperCont: return "UPPER-CONT";
                case SessionContext.SessionHighBo: return "SESS-HIGH-BO";
                default: return "UNKNOWN";
            }
        }

        private int GetActiveAnchorIndex()
        {
            switch (AvwapAnchor)
            {
                case AvwapAnchorType.SessionOpen: return rthOpenBarIdx;
                case AvwapAnchorType.SessionHigh: return sessionHighBarIdx;
                case AvwapAnchorType.SessionLow: return sessionLowBarIdx;
                default: return -1;
            }
        }

        private bool IsConstantVolumeBarEnvironment(double currentBarVolume)
        {
            if (!AutoDisableBarVolumeFiltersOnConstantVolume)
                return false;

            if (!adaptiveReady || currentBarVolume <= 0)
                return false;

            return adaptiveVolumeStdDev <= Math.Max(1.0, currentBarVolume * 0.001);
        }

        private AdaptiveContextFamily GetAdaptiveContextFamily(SessionLocationBucket sessionBucket, ValueAreaContext vaContext)
        {
            bool cheapVa = IsCheapValueAreaContext(vaContext);
            bool neutralVa = IsNeutralValueAreaContext(vaContext);
            bool richVa = IsRichValueAreaContext(vaContext);

            switch (sessionBucket)
            {
                case SessionLocationBucket.Basement:
                    if (cheapVa) return AdaptiveContextFamily.BelowValueReversal;
                    if (neutralVa) return AdaptiveContextFamily.BasementValueReclaim;
                    if (richVa) return AdaptiveContextFamily.LocationConflict;
                    break;

                case SessionLocationBucket.Lower:
                    if (cheapVa) return AdaptiveContextFamily.BelowValueReversal;
                    if (neutralVa) return AdaptiveContextFamily.WithGrainContinuation;
                    if (richVa) return AdaptiveContextFamily.LocationConflict;
                    break;

                case SessionLocationBucket.Mid:
                    if (cheapVa) return AdaptiveContextFamily.LocationConflict;
                    if (neutralVa) return AdaptiveContextFamily.MidRangeChop;
                    if (richVa) return AdaptiveContextFamily.LocationConflict;
                    break;

                case SessionLocationBucket.Upper:
                    if (cheapVa) return AdaptiveContextFamily.LocationConflict;
                    if (neutralVa) return AdaptiveContextFamily.UpperValueFriction;
                    if (richVa) return AdaptiveContextFamily.UpperValueFriction;  // Was CeilingBreakout — reclassified per Logs 17 analysis
                    break;

                case SessionLocationBucket.Ceiling:
                    if (cheapVa) return AdaptiveContextFamily.LocationConflict;
                    if (neutralVa) return AdaptiveContextFamily.UpperValueFriction;
                    if (richVa) return AdaptiveContextFamily.UpperValueFriction;  // Was CeilingBreakout — reclassified per Logs 17 analysis
                    break;
            }

            return AdaptiveContextFamily.Unknown;
        }

        private string GetAdaptiveContextFamilyString(AdaptiveContextFamily family)
        {
            switch (family)
            {
                case AdaptiveContextFamily.BasementValueReclaim: return "BASEMENT-VALUE";
                case AdaptiveContextFamily.BelowValueReversal: return "BELOW-VAL-REV";
                case AdaptiveContextFamily.WithGrainContinuation: return "WITH-GRAIN";
                case AdaptiveContextFamily.MidRangeChop: return "MID-CHOP";
                case AdaptiveContextFamily.UpperValueFriction: return "UPPER-FRICTION";
                case AdaptiveContextFamily.CeilingBreakout: return "CEILING-BO";
                case AdaptiveContextFamily.LocationConflict: return "LOCATION-CONFLICT";
                case AdaptiveContextFamily.CeilingValueReject: return "CEILING-REJECT";
                case AdaptiveContextFamily.AboveValueReversal: return "ABOVE-VAH-REV";
                case AdaptiveContextFamily.WithGrainShortContinuation: return "SHORT-CONT";
                case AdaptiveContextFamily.LowerValueFriction: return "LOWER-FRICTION";
                case AdaptiveContextFamily.BasementBreakdown: return "BASEMENT-BREAK";
                default: return "UNKNOWN";
            }
        }

        private AdaptiveContextFamily GetAdaptiveContextFamilyShort(SessionLocationBucket sessionBucket, ValueAreaContext vaContext)
        {
            // Short-side: selling rallies/breakdowns
            if (sessionBucket == SessionLocationBucket.Ceiling || sessionBucket == SessionLocationBucket.Upper)
            {
                if (vaContext == ValueAreaContext.AboveVAH || vaContext == ValueAreaContext.AtVAH)
                    return AdaptiveContextFamily.CeilingValueReject;
                if (vaContext == ValueAreaContext.InValue || vaContext == ValueAreaContext.AtPOC)
                    return AdaptiveContextFamily.LowerValueFriction;
            }

            if (vaContext == ValueAreaContext.BelowVAL || vaContext == ValueAreaContext.AtVAL)
            {
                if (sessionBucket == SessionLocationBucket.Upper || sessionBucket == SessionLocationBucket.Mid)
                    return AdaptiveContextFamily.AboveValueReversal;
            }

            if (sessionBucket == SessionLocationBucket.Mid && (vaContext == ValueAreaContext.InValue || vaContext == ValueAreaContext.AtPOC))
                return AdaptiveContextFamily.WithGrainShortContinuation;

            if (sessionBucket == SessionLocationBucket.Lower || sessionBucket == SessionLocationBucket.Basement)
            {
                if (vaContext == ValueAreaContext.InValue || vaContext == ValueAreaContext.AtPOC || vaContext == ValueAreaContext.BelowVAL)
                    return AdaptiveContextFamily.LowerValueFriction;
                if (vaContext == ValueAreaContext.AboveVAH || vaContext == ValueAreaContext.AtVAH)
                    return AdaptiveContextFamily.BasementBreakdown;
            }

            if (sessionBucket == SessionLocationBucket.Ceiling && (vaContext == ValueAreaContext.AboveVAH || vaContext == ValueAreaContext.AtVAH))
                return AdaptiveContextFamily.CeilingValueReject;

            return AdaptiveContextFamily.Unknown;
        }

        private AdaptiveRuleProfile GetAdaptiveRuleProfileShort(AdaptiveContextFamily family, bool disableBarVolumeDependentFilters)
        {
            // Map short-side families to their long-side counterparts for profile lookup
            // The user will calibrate these separately via backtesting
            AdaptiveContextFamily mappedFamily;
            switch (family)
            {
                case AdaptiveContextFamily.CeilingValueReject:
                    mappedFamily = AdaptiveContextFamily.BasementValueReclaim;
                    break;
                case AdaptiveContextFamily.AboveValueReversal:
                    mappedFamily = AdaptiveContextFamily.BelowValueReversal;
                    break;
                case AdaptiveContextFamily.WithGrainShortContinuation:
                    mappedFamily = AdaptiveContextFamily.WithGrainContinuation;
                    break;
                case AdaptiveContextFamily.LowerValueFriction:
                    mappedFamily = AdaptiveContextFamily.UpperValueFriction;
                    break;
                case AdaptiveContextFamily.BasementBreakdown:
                    mappedFamily = AdaptiveContextFamily.CeilingBreakout;
                    break;
                default:
                    mappedFamily = family;
                    break;
            }
            return GetAdaptiveRuleProfile(mappedFamily, disableBarVolumeDependentFilters);
        }

        private AdaptiveRuleProfile GetAdaptiveRuleProfile(AdaptiveContextFamily family, bool disableBarVolumeDependentFilters)
        {
            AdaptiveRuleProfile profile = new AdaptiveRuleProfile();
            profile.DisableBarVolumeDependentFilters = disableBarVolumeDependentFilters;
            profile.UseMinEscape = S3_UseMinEscape;
            profile.MinEscape = S3_MinEscape;
            profile.UseMaxEscape = S3_UseMaxEscape;
            profile.MaxEscape = S3_MaxEscape;
            profile.UseMinDomVol = S3_UseMinDomVol;
            profile.MinDomVol = S3_MinDomVol;
            profile.UseMaxDomVol = S3_UseMaxDomVol;
            profile.MaxDomVol = S3_MaxDomVol;
            profile.MinRatio = 0;
            profile.RequireImprovingDelta = false;
            profile.RequirePositiveBarDelta = false;
            profile.RequirePocLift = false;
            profile.RequireAvwapReclaim = false;
            profile.UseCeilingTrapKillSwitch = false;
            profile.CeilingTrapAbsorptionPct = AdaptiveCeilingTrapAbsorptionPct;

            switch (family)
            {
                case AdaptiveContextFamily.BasementValueReclaim:
                    profile.UseMinEscape = true;
                    profile.MinEscape = AdaptiveBasementMinEscape;
                    profile.UseMaxEscape = false;
                    profile.UseMinDomVol = true;
                    profile.MinDomVol = AdaptiveBasementMinDomVol;
                    profile.UseMaxDomVol = false;
                    profile.RequireImprovingDelta = true;
                    profile.RequireAvwapReclaim = true;
                    break;

                case AdaptiveContextFamily.BelowValueReversal:
                    profile.UseMinEscape = true;
                    profile.MinEscape = AdaptiveBasementMinEscape;
                    profile.UseMaxEscape = true;
                    profile.MaxEscape = AdaptiveMidRangeMaxEscape;
                    profile.UseMinDomVol = true;
                    profile.MinDomVol = Math.Max(AdaptiveBasementMinDomVol, AdaptiveContinuationMinDomVol);
                    profile.UseMaxDomVol = false;
                    profile.MinRatio = AdaptiveMidRangeMinRatio;
                    profile.RequireImprovingDelta = true;
                    profile.RequirePocLift = true;
                    profile.RequireAvwapReclaim = true;
                    break;

                case AdaptiveContextFamily.WithGrainContinuation:
                    profile.UseMinEscape = true;
                    profile.MinEscape = AdaptiveCeilingMinEscape;
                    profile.UseMaxEscape = true;
                    profile.MaxEscape = AdaptiveCeilingMaxEscape;
                    profile.UseMinDomVol = true;
                    profile.MinDomVol = AdaptiveContinuationMinDomVol;
                    profile.UseMaxDomVol = false;
                    break;

                case AdaptiveContextFamily.MidRangeChop:
                    profile.UseMinEscape = true;
                    profile.MinEscape = AdaptiveMidRangeMinEscape;
                    profile.UseMaxEscape = true;
                    profile.MaxEscape = AdaptiveMidRangeMaxEscape;
                    profile.UseMinDomVol = true;
                    profile.MinDomVol = AdaptiveMidRangeMinDomVol;
                    profile.UseMaxDomVol = false;
                    profile.MinRatio = AdaptiveMidRangeMinRatio;
                    profile.RequireImprovingDelta = true;
                    profile.RequirePositiveBarDelta = true;
                    profile.RequirePocLift = false;
                    break;

                case AdaptiveContextFamily.UpperValueFriction:
                    profile.UseMinEscape = true;
                    profile.MinEscape = AdaptiveMidRangeMinEscape;
                    profile.UseMaxEscape = true;
                    profile.MaxEscape = AdaptiveMidRangeMaxEscape;
                    profile.UseMinDomVol = true;
                    profile.MinDomVol = Math.Max(AdaptiveContinuationMinDomVol, AdaptiveMidRangeMinDomVol);
                    profile.UseMaxDomVol = false;
                    profile.MinRatio = AdaptiveMidRangeMinRatio;
                    profile.RequireImprovingDelta = true;
                    profile.RequirePositiveBarDelta = false;
                    profile.RequirePocLift = false;
                    profile.RequireAvwapReclaim = true;
                    profile.UseCeilingTrapKillSwitch = true;
                    break;

                case AdaptiveContextFamily.CeilingBreakout:
                    profile.UseMinEscape = true;
                    profile.MinEscape = AdaptiveCeilingMinEscape;
                    profile.UseMaxEscape = true;
                    profile.MaxEscape = AdaptiveCeilingMaxEscape;
                    profile.UseMinDomVol = false; // DomVol OR Ratio override
                    profile.MinDomVol = AdaptiveCeilingMinDomVol;
                    profile.UseMaxDomVol = false;
                    profile.MinRatio = AdaptiveCeilingMinRatio;
                    profile.UseCeilingTrapKillSwitch = true;
                    break;

                case AdaptiveContextFamily.LocationConflict:
                    profile.UseMinEscape = true;
                    profile.MinEscape = AdaptiveCeilingMinEscape;
                    profile.UseMaxEscape = true;
                    profile.MaxEscape = AdaptiveCeilingMaxEscape;
                    profile.UseMinDomVol = true;
                    profile.MinDomVol = Math.Max(AdaptiveCeilingMinDomVol, AdaptiveMidRangeMinDomVol);
                    profile.UseMaxDomVol = false;
                    profile.MinRatio = Math.Max(AdaptiveCeilingMinRatio, AdaptiveMidRangeMinRatio);
                    profile.RequireImprovingDelta = true;
                    profile.RequirePositiveBarDelta = false;
                    profile.RequirePocLift = false;
                    profile.RequireAvwapReclaim = true;
                    profile.UseCeilingTrapKillSwitch = true;
                    break;
            }

            return profile;
        }

        private double GetTimeAdjustedBaseline()
        {
            int currentHour = CurrentBar >= 1 ? Time[1].Hour : Time[0].Hour;
            List<double> hourlyVolumes;
            if (volumeByHour.TryGetValue(currentHour, out hourlyVolumes) 
                && hourlyVolumes.Count >= MinHourlySamplesForBaseline)
            {
                double sum = 0;
                for (int i = 0; i < hourlyVolumes.Count; i++)
                    sum += hourlyVolumes[i];
                return sum / hourlyVolumes.Count;
            }
            
            return adaptiveReady ? adaptiveVolumeBaseline : S3_MinVolume;
        }

        private double CalculateStackRecency(int stackTopTick, int stackSize, int barHighTick, int barLowTick)
        {
            if (barHighTick <= barLowTick) return DefaultStackRecency;
            
            double stackMidTick = stackTopTick - ((stackSize - 1.0) / 2.0);
            double distanceFromHigh = barHighTick - stackMidTick;
            double barRange = barHighTick - barLowTick;
            double recency = 1.0 - (distanceFromHigh / barRange);
            
            if (recency < 0) return 0;
            if (recency > 1.0) return 1.0;
            return recency;
        }

        private double CalculateStackRecencyShort(int stackTopTick, int stackSize, int barHighTick, int barLowTick)
        {
            if (barHighTick <= barLowTick) return DefaultStackRecency;

            double stackMidTick = stackTopTick - ((stackSize - 1.0) / 2.0);
            double distanceFromLow = stackMidTick - barLowTick;
            double barRange = barHighTick - barLowTick;
            double recency = 1.0 - (distanceFromLow / barRange);

            if (recency < 0) return 0;
            if (recency > 1.0) return 1.0;
            return recency;
        }

        private void GetFollowThroughStats(out double rate, out double avgMfe, out double avgMae, out int sampleCount)
        {
            sampleCount = recentTradeResults.Count;

            if (sampleCount == 0)
            {
                rate = 0;
                avgMfe = 0;
                avgMae = 0;
                return;
            }

            int successCount = 0;
            double mfeSum = 0;
            double maeSum = 0;

            foreach (var result in recentTradeResults)
            {
                if (result.MfeTicks >= FollowThroughMinTicks)
                    successCount++;
                mfeSum += result.MfeTicks;
                maeSum += result.MaeTicks;
            }

            rate = (double)successCount / sampleCount;
            avgMfe = mfeSum / sampleCount;
            avgMae = maeSum / sampleCount;
        }

        private void RecordTradeResult(Trade trade, string context, string volRegime, double stackRecency, int clusterCount)
        {
            double pnlTicks = trade.ProfitPoints / TickSize;

            var result = new TradeResult
            {
                MfeTicks = trade.MfePoints / TickSize,
                MaeTicks = trade.MaePoints / TickSize,
                PnlTicks = pnlTicks,
                Context = context,
                VolRegime = volRegime,
                StackRecency = stackRecency,
                ClusterCount = clusterCount,
                EntryTime = trade.Entry.Time
            };

            recentTradeResults.Enqueue(result);
            if (recentTradeResults.Count > maxTradeMemory)
                recentTradeResults.Dequeue();

            dailyTradeCount++;
            dailyPnlTicks += pnlTicks;
            if (pnlTicks > 0) dailyWins++;
            else if (pnlTicks < 0) dailyLosses++;

            UpdateDailyDictionary(dailyContextCounts, dailyContextPnl, context, pnlTicks);
            UpdateDailyDictionary(dailyRegimeCounts, dailyRegimePnl, volRegime, pnlTicks);

            string clusterKey = clusterCount >= 2 ? "Clustered" : "Isolated";
            UpdateDailyDictionary(dailyClusterCounts, dailyClusterPnl, clusterKey, pnlTicks);
        }

        private void UpdateDailyDictionary(Dictionary<string, int> countDict, Dictionary<string, double> pnlDict, string key, double pnlTicks)
        {
            int currentCount;
            if (countDict.TryGetValue(key, out currentCount))
            {
                countDict[key] = currentCount + 1;
                pnlDict[key] = pnlDict[key] + pnlTicks;
            }
            else
            {
                countDict[key] = 1;
                pnlDict[key] = pnlTicks;
            }
        }

        private MarketRegime GetMarketRegime(NinjaTrader.NinjaScript.BarsTypes.VolumetricBarsType vBarsType)
        {
            const int divLookback = 5;
            if (CurrentBar < divLookback + 1)
                return MarketRegime.Flat;

            double pChange = Close[1] - Close[1 + divLookback];

            double dChange = 0;
            for (int i = 0; i < divLookback; i++)
            {
                dChange += vBarsType.Volumes[CurrentBar - 1 - i].BarDelta;
            }

            if (pChange >= 0 && dChange < 0) return MarketRegime.BullDiv;
            if (pChange > 0 && dChange > 0) return MarketRegime.BullConv;
            if (pChange <= 0 && dChange > 0) return MarketRegime.BearDiv;
            if (pChange < 0 && dChange < 0) return MarketRegime.BearConv;
            
            return MarketRegime.Flat;
        }

        private string GetMarketRegimeString(MarketRegime regime)
        {
            switch (regime)
            {
                case MarketRegime.BullDiv: return "BULL-DIV";
                case MarketRegime.BearDiv: return "BEAR-DIV";
                case MarketRegime.BullConv: return "BULL-CONV";
                case MarketRegime.BearConv: return "BEAR-CONV";
                case MarketRegime.Flat: return "FLAT";
                default: return "UNKNOWN";
            }
        }

        private bool IsRegimeAllowed(MarketRegime regime)
        {
            switch (regime)
            {
                case MarketRegime.BullDiv: return AllowBullDiv;
                case MarketRegime.BearDiv: return AllowBearDiv;
                case MarketRegime.BullConv: return AllowBullConv;
                case MarketRegime.BearConv: return AllowBearConv;
                default: return true;
            }
        }

        private void UpdateMicrostructureRegime(double r1k)
        {
            r1kRollingBuffer.Enqueue(r1k);
            if (r1kRollingBuffer.Count > R1kRollingWindowBars)
                r1kRollingBuffer.Dequeue();

            if (r1kRollingBuffer.Count >= R1kRollingWindowBars)
            {
                rollingR1k = r1kRollingBuffer.Average();
                currentMicroRegime = ClassifyMicroRegime(rollingR1k);
            }
            else
            {
                rollingR1k = 0.0;
                currentMicroRegime = MicrostructureRegime.Warmup;
            }
        }

        private MicrostructureRegime ClassifyMicroRegime(double roll20)
        {
            if (roll20 < RegimeDenseThreshold) return MicrostructureRegime.Dense;
            if (roll20 > RegimeThinThreshold) return MicrostructureRegime.Thin;
            return MicrostructureRegime.Normal;
        }

        private string GetMicroRegimeString(MicrostructureRegime regime)
        {
            switch (regime)
            {
                case MicrostructureRegime.Dense:  return "DENSE";
                case MicrostructureRegime.Normal: return "NORMAL";
                case MicrostructureRegime.Thin:   return "THIN";
                default:                          return "WARMUP";
            }
        }

        private bool IsMicroRegimeAllowed()
        {
            if (!EnableRegimeFilter) return true;
            switch (currentMicroRegime)
            {
                case MicrostructureRegime.Dense:  return AllowDenseRegime;
                case MicrostructureRegime.Normal: return AllowNormalMicroRegime;
                case MicrostructureRegime.Thin:   return AllowThinRegime;
                case MicrostructureRegime.Warmup: return AllowWarmupRegime;
                default: return true; // Fallback for any future regime values not yet enumerated
            }
        }
        #endregion

        #region Helper Methods - Climax/Exhaustion
        private void CalculateClimaxExhaustion(double currentBarVolume, double currentBarRange, double volZScore, 
            out bool isClimax, out bool isExhaustion, out double climaxScore, out double exhaustionScore)
        {
            isClimax = false;
            isExhaustion = false;
            climaxScore = 0;
            exhaustionScore = 0;

            if (!barRangeBufferReady || avgBarRange <= 0) return;

            double rangeRatio = currentBarRange / avgBarRange;
            bool volumeIsHigh = volZScore >= ClimaxVolumeZScoreThreshold;
            bool rangeIsLow = rangeRatio < ClimaxRangeRatioMax;

            if (volumeIsHigh && rangeIsLow)
            {
                isClimax = true;
                double volComponent = Math.Min(1.0, volZScore / 3.0);
                double rangeComponent = 1.0 - rangeRatio;
                climaxScore = (volComponent + rangeComponent) / 2.0;
            }

            if (prevBarVolume > 0 && currentBarVolume > 0)
            {
                double volumeDropRatio = currentBarVolume / prevBarVolume;
                if (volumeDropRatio < ExhaustionVolumeDropRatio)
                {
                    isExhaustion = true;
                    exhaustionScore = 1.0 - volumeDropRatio;
                }
            }

            prevBarVolume = currentBarVolume;
            prevBarRange = currentBarRange;
        }

        private bool EvaluateClimaxFilter(bool isClimax, bool isExhaustion)
        {
            if (!UseClimaxFilter && !UseExhaustionFilter) return true;

            bool passClimax = true;
            bool passExhaustion = true;

            if (UseClimaxFilter)
            {
                if (BlockEntryOnClimaxBar && isClimax)
                    passClimax = false;

                if (RequirePostClimaxEntry && !prevBarWasClimax)
                    passClimax = false;
            }

            if (UseExhaustionFilter)
            {
                if (RequireExhaustionSetup && !isExhaustion)
                    passExhaustion = false;
            }

            return passClimax && passExhaustion;
        }
        #endregion

        #region Helper Methods - Adaptive 40 Range Filter
        private bool EvaluateAdaptive40RangeFilter(SessionContext sessionContext, DeltaMomentum deltaMomentum, int netImbCount)
        {
            if (!UseAdaptive40RangeFilter) return true;
            if (currentMicroRegime != MicrostructureRegime.Normal) return true;

            if (Block_LowerCont_AccelBuy && sessionContext == SessionContext.LowerCont && deltaMomentum == DeltaMomentum.AccelBuy)
                return false;
            if (Block_MidRange_AccelBuy && sessionContext == SessionContext.MidRange && deltaMomentum == DeltaMomentum.AccelBuy)
                return false;
            if (Block_NIC1 && netImbCount == 1)
                return false;

            return true;
        }
        #endregion

        #region Helper Methods - ES 8-Range Filter
        private bool EvaluateESRangeFilter(SessionContext sessionContext, DeltaMomentum deltaMomentum, AdaptiveContextFamily adaptiveContextFamily, VolatilityRegime volatilityRegime, double avwapDistTicks)
        {
            if (!UseESRangeFilter) return true;

            // F1: Block SESS-HIGH-BO + ACCEL-BUY
            if (ES_Block_HighBO_AccelBuy && sessionContext == SessionContext.SessionHighBo && deltaMomentum == DeltaMomentum.AccelBuy)
                return false;

            // F4: Block UPPER-FRICTION + QUIET + ACCEL-BUY
            if (ES_Block_UpperFriction_Quiet_AccelBuy && adaptiveContextFamily == AdaptiveContextFamily.UpperValueFriction && volatilityRegime == VolatilityRegime.Quiet && deltaMomentum == DeltaMomentum.AccelBuy)
                return false;

            // F5: Block AVWAP EXTREME tier
            if (ES_Block_AvwapExtreme && GetAvwapZoneLabel(avwapDistTicks) == "EXTREME")
                return false;

            return true;
        }
        #endregion

        #region Helper Methods - Value Area (NYSE Session)
        private bool IsWithinNYSESession(DateTime time)
        {
            TimeSpan timeOfDay = time.TimeOfDay;
            return timeOfDay >= NYSEOpenTime && timeOfDay <= NYSECloseTime;
        }

        private bool IsWithinPremarket(DateTime time)
        {
            TimeSpan timeOfDay = time.TimeOfDay;
            return timeOfDay >= PremarketStartTime && timeOfDay <= PremarketEndTime;
        }

        private bool IsWithinInitialBalance(DateTime time)
        {
            TimeSpan timeOfDay = time.TimeOfDay;
            return timeOfDay >= NYSEOpenTime && timeOfDay <= InitialBalanceEndTime;
        }

        private void ResetKeyLevelTracking()
        {
            premarketHigh = double.MinValue;
            premarketLow = double.MaxValue;
            premarketInitialized = false;
            initialBalanceHigh = double.MinValue;
            initialBalanceLow = double.MaxValue;
            initialBalanceLocked = false;
        }

        private void UpdateKeyLevelTrackingConfirmedBar()
        {
            if (CurrentBar < 1)
                return;

            DateTime confirmedTime = Time[1];
            double confirmedHigh = High[1];
            double confirmedLow = Low[1];

            if (IsWithinPremarket(confirmedTime))
            {
                if (!premarketInitialized)
                {
                    premarketHigh = confirmedHigh;
                    premarketLow = confirmedLow;
                    premarketInitialized = true;
                }
                else
                {
                    if (confirmedHigh > premarketHigh) premarketHigh = confirmedHigh;
                    if (confirmedLow < premarketLow) premarketLow = confirmedLow;
                }
            }

            if (IsWithinInitialBalance(confirmedTime))
            {
                if (initialBalanceHigh == double.MinValue || confirmedHigh > initialBalanceHigh)
                    initialBalanceHigh = confirmedHigh;
                if (initialBalanceLow == double.MaxValue || confirmedLow < initialBalanceLow)
                    initialBalanceLow = confirmedLow;
            }
            else if (!initialBalanceLocked && initialBalanceHigh != double.MinValue && initialBalanceLow != double.MaxValue)
            {
                initialBalanceLocked = true;
            }
        }

        private void ConsiderNearestKeyLevel(string levelName, double signedTicks, ref string bestName, ref double bestAbsTicks)
        {
            if (signedTicks == double.MaxValue)
                return;

            double absTicks = Math.Abs(signedTicks);
            if (absTicks < bestAbsTicks)
            {
                bestAbsTicks = absTicks;
                bestName = levelName;
            }
        }

        private string BuildKeyLevelSummary(
            bool nearVWAP, double distVWAP,
            bool nearPDH, double distPDH,
            bool nearPDL, double distPDL,
            bool nearIBH, double distIBH,
            bool nearIBL, double distIBL,
            bool nearPMH, double distPMH,
            bool nearPML, double distPML,
            bool nearPOC, double distPOC)
        {
            var parts = new List<string>();

            if (nearVWAP) parts.Add(string.Format("VWAP({0})", FormatSignedTicks(distVWAP)));
            if (nearPDH) parts.Add(string.Format("PDH({0})", FormatSignedTicks(distPDH)));
            if (nearPDL) parts.Add(string.Format("PDL({0})", FormatSignedTicks(distPDL)));
            if (nearIBH) parts.Add(string.Format("IBH({0})", FormatSignedTicks(distIBH)));
            if (nearIBL) parts.Add(string.Format("IBL({0})", FormatSignedTicks(distIBL)));
            if (nearPMH) parts.Add(string.Format("PMH({0})", FormatSignedTicks(distPMH)));
            if (nearPML) parts.Add(string.Format("PML({0})", FormatSignedTicks(distPML)));
            if (nearPOC) parts.Add(string.Format("POC({0})", FormatSignedTicks(distPOC)));

            return parts.Count == 0 ? "NONE" : string.Join(" | ", parts);
        }

        private bool EvaluateKeyLevelGate(
            bool nearVWAP, bool nearPDH, bool nearPDL, bool nearIBH, bool nearIBL, bool nearPMH, bool nearPML, bool nearPOC,
            double deltaPctOfVolume, bool absorptionStrong, DateTime barTime, SessionLocationBucket sessionBucket)
        {
            bool nearAnyAllowed =
                (KL_AllowVWAP && nearVWAP) ||
                (KL_AllowPDH && nearPDH) ||
                (KL_AllowPDL && nearPDL) ||
                (KL_AllowIBH && nearIBH) ||
                (KL_AllowIBL && nearIBL) ||
                (KL_AllowPMH && nearPMH) ||
                (KL_AllowPML && nearPML) ||
                (KL_AllowPOC && nearPOC);

            if (!UseKeyLevelGate)
                return true;

            if (!nearAnyAllowed)
                return false;

            if (KL_AvoidMiddayChop)
            {
                TimeSpan tod = barTime.TimeOfDay;
                if (tod >= KL_MiddayStart.TimeOfDay && tod <= KL_MiddayEnd.TimeOfDay)
                    return false;
            }

            if (KL_RequireDeltaAgreement && deltaPctOfVolume <= 0)
                return false;

            bool reversalBucket = sessionBucket == SessionLocationBucket.Basement || sessionBucket == SessionLocationBucket.Lower;
            if (KL_RequireAbsorptionForReversal && reversalBucket && !absorptionStrong)
                return false;

            return true;
        }

        private void UpdateNYSEValueArea(double price, double volume, DateTime barTime)
        {
            DateTime barDate = barTime.Date;
            if (barDate != lastNYSESessionDate)
            {
                ResetNYSEValueArea();
                lastNYSESessionDate = barDate;
            }

            if (!IsWithinNYSESession(barTime)) return;
            if (volume <= 0) return;

            int priceTick = (int)Math.Round(price / TickSize);

            double existingVol;
            if (nyseSessionVolumeByTick.TryGetValue(priceTick, out existingVol))
                nyseSessionVolumeByTick[priceTick] = existingVol + volume;
            else
                nyseSessionVolumeByTick[priceTick] = volume;

            nyseSessionTotalVolume += volume;

            if (nyseSessionVolumeByTick.Count >= MinTicksForValueArea)
                CalculateNYSEValueArea();
        }

        private void CalculateNYSEValueArea()
        {
            if (nyseSessionTotalVolume <= 0 || nyseSessionVolumeByTick.Count < MinTicksForValueArea)
            {
                nyseValueAreaValid = false;
                return;
            }

            int pocTick = 0;
            double maxVol = 0;
            foreach (var kvp in nyseSessionVolumeByTick)
            {
                if (kvp.Value > maxVol)
                {
                    maxVol = kvp.Value;
                    pocTick = kvp.Key;
                }
            }
            nyseSessionPOC = pocTick * TickSize;

            List<int> sortedTicks = new List<int>(nyseSessionVolumeByTick.Keys);
            sortedTicks.Sort();

            int pocIndex = sortedTicks.IndexOf(pocTick);
            if (pocIndex < 0)
            {
                nyseValueAreaValid = false;
                return;
            }

            double targetVolume = nyseSessionTotalVolume * ValueAreaPercentage;
            double capturedVolume = nyseSessionVolumeByTick[pocTick];

            int upperIndex = pocIndex;
            int lowerIndex = pocIndex;

            while (capturedVolume < targetVolume && (upperIndex < sortedTicks.Count - 1 || lowerIndex > 0))
            {
                double upperVol = 0;
                double lowerVol = 0;

                if (upperIndex < sortedTicks.Count - 1)
                    nyseSessionVolumeByTick.TryGetValue(sortedTicks[upperIndex + 1], out upperVol);
                
                if (lowerIndex > 0)
                    nyseSessionVolumeByTick.TryGetValue(sortedTicks[lowerIndex - 1], out lowerVol);

                if (upperVol >= lowerVol && upperIndex < sortedTicks.Count - 1)
                {
                    upperIndex++;
                    capturedVolume += nyseSessionVolumeByTick[sortedTicks[upperIndex]];
                }
                else if (lowerIndex > 0)
                {
                    lowerIndex--;
                    capturedVolume += nyseSessionVolumeByTick[sortedTicks[lowerIndex]];
                }
                else
                {
                    break;
                }
            }

            nyseSessionVAH = sortedTicks[upperIndex] * TickSize;
            nyseSessionVAL = sortedTicks[lowerIndex] * TickSize;
            nyseValueAreaValid = true;
        }

        private ValueAreaContext GetValueAreaContext(double price)
        {
            if (!nyseValueAreaValid) return ValueAreaContext.NoVA;

            double distToPOC = Math.Abs(price - nyseSessionPOC) / TickSize;
            double distToVAH = Math.Abs(price - nyseSessionVAH) / TickSize;
            double distToVAL = Math.Abs(price - nyseSessionVAL) / TickSize;

            if (distToPOC <= ValueAreaPOCProximityTicks) return ValueAreaContext.AtPOC;
            if (distToVAH <= ValueAreaEdgeProximityTicks && price >= nyseSessionVAH) return ValueAreaContext.AtVAH;
            if (distToVAL <= ValueAreaEdgeProximityTicks && price <= nyseSessionVAL) return ValueAreaContext.AtVAL;

            if (price > nyseSessionVAH) return ValueAreaContext.AboveVAH;
            if (price < nyseSessionVAL) return ValueAreaContext.BelowVAL;
            return ValueAreaContext.InValue;
        }

        private string GetValueAreaContextString(ValueAreaContext context)
        {
            switch (context)
            {
                case ValueAreaContext.NoVA: return "NO-VA";
                case ValueAreaContext.BelowVAL: return "BELOW-VAL";
                case ValueAreaContext.AtVAL: return "AT-VAL";
                case ValueAreaContext.InValue: return "IN-VALUE";
                case ValueAreaContext.AtPOC: return "AT-POC";
                case ValueAreaContext.AtVAH: return "AT-VAH";
                case ValueAreaContext.AboveVAH: return "ABOVE-VAH";
                default: return "UNKNOWN";
            }
        }

        private bool EvaluateValueAreaFilter(ValueAreaContext context, double price)
        {
            if (!UseValueAreaFilter) return true;

            bool pass = true;

            switch (context)
            {
                case ValueAreaContext.NoVA:      if (!VA_AllowNoVA) pass = false; break;
                case ValueAreaContext.BelowVAL:  if (!VA_AllowBelowVAL) pass = false; break;
                case ValueAreaContext.AtVAL:     if (!VA_AllowAtVAL) pass = false; break;
                case ValueAreaContext.InValue:   if (!VA_AllowInValue) pass = false; break;
                case ValueAreaContext.AtPOC:     if (!VA_AllowAtPOC) pass = false; break;
                case ValueAreaContext.AtVAH:     if (!VA_AllowAtVAH) pass = false; break;
                case ValueAreaContext.AboveVAH:  if (!VA_AllowAboveVAH) pass = false; break;
            }

            if (VA_RequirePOCTouch && VA_POCTouchLookbackBars > 0 && nyseValueAreaValid)
            {
                bool pocTouched = false;
                for (int i = 1; i <= Math.Min(VA_POCTouchLookbackBars, CurrentBar - 1); i++)
                {
                    if (Low[i] <= nyseSessionPOC && High[i] >= nyseSessionPOC)
                    {
                        pocTouched = true;
                        break;
                    }
                }
                if (!pocTouched) pass = false;
            }

            return pass;
        }
        #endregion

        #region Helper Methods - Delta Velocity
        private void UpdateDeltaVelocity(double currentBarDelta)
        {
            if (deltaVelocityHistory == null || deltaVelocityHistory.Length < 3)
            {
                deltaVelocityHistory = new double[DeltaVelocityLookback + 2];
            }

            deltaVelocityHistory[deltaVelocityIndex] = currentBarDelta;
            deltaVelocityIndex = (deltaVelocityIndex + 1) % deltaVelocityHistory.Length;

            if (CurrentBar >= DeltaVelocityLookback + 2)
                deltaVelocityReady = true;

            if (!deltaVelocityReady) return;

            int len = deltaVelocityHistory.Length;
            int curIdx = (deltaVelocityIndex - 1 + len) % len;
            int prevIdx = (deltaVelocityIndex - 2 + len) % len;
            int prev2Idx = (deltaVelocityIndex - 3 + len) % len;

            double curDelta = deltaVelocityHistory[curIdx];
            double prevDelta = deltaVelocityHistory[prevIdx];
            double prev2Delta = deltaVelocityHistory[prev2Idx];

            currentDeltaROC = curDelta - prevDelta;
            double prevDeltaROC = prevDelta - prev2Delta;
            currentDeltaAccel = currentDeltaROC - prevDeltaROC;

            double rocNorm = currentDeltaROC / DeltaROCNormalizationFactor;
            if (rocNorm > 1.0) rocNorm = 1.0;
            if (rocNorm < -1.0) rocNorm = -1.0;

            double accelNorm = currentDeltaAccel / DeltaAccelNormalizationFactor;
            if (accelNorm > 1.0) accelNorm = 1.0;
            if (accelNorm < -1.0) accelNorm = -1.0;

            deltaVelocityScore = (rocNorm * DeltaVelocityROCWeight) + (accelNorm * DeltaVelocityAccelWeight);

            double rocThreshold = 2.0; 
            double accelThreshold = 2.0; 

            if (Math.Abs(currentDeltaROC) <= rocThreshold && Math.Abs(currentDeltaAccel) <= accelThreshold)
                currentDeltaMomentum = DeltaMomentum.Neutral;
            else if (currentDeltaROC > 0 && currentDeltaAccel > 0)
                currentDeltaMomentum = DeltaMomentum.AccelBuy;
            else if (currentDeltaROC > 0 && currentDeltaAccel <= 0)
                currentDeltaMomentum = DeltaMomentum.DecelBuy;
            else if (currentDeltaROC <= 0 && currentDeltaAccel > 0)
                currentDeltaMomentum = DeltaMomentum.DecelSell;
            else if (currentDeltaROC <= 0 && currentDeltaAccel <= 0)
                currentDeltaMomentum = DeltaMomentum.AccelSell;
            else
                currentDeltaMomentum = DeltaMomentum.Neutral;
        }

        private string GetDeltaMomentumString(DeltaMomentum momentum)
        {
            switch (momentum)
            {
                case DeltaMomentum.AccelBuy: return "ACCEL-BUY";
                case DeltaMomentum.DecelBuy: return "DECEL-BUY";
                case DeltaMomentum.DecelSell: return "DECEL-SELL";
                case DeltaMomentum.AccelSell: return "ACCEL-SELL";
                case DeltaMomentum.Neutral: return "NEUTRAL";
                default: return "UNKNOWN";
            }
        }

        private bool EvaluateDeltaVelocityFilter()
        {
            if (!UseDeltaVelocityFilter) return true;
            if (!deltaVelocityReady) return true;

            bool pass = true;

            if (currentDeltaROC < DV_MinDeltaROC)
                pass = false;

            if (DV_RequirePositiveAccel && currentDeltaAccel <= 0)
                pass = false;

            if (DV_BlockAcceleratingSelling && currentDeltaMomentum == DeltaMomentum.AccelSell)
                pass = false;

            return pass;
        }
        #endregion

        #region Helper Methods - Trading Logic
        private bool IsWithinActiveSession(DateTime currentTime)
        {
            if (!UseSessionFilter) return true;
            TimeSpan now = currentTime.TimeOfDay;
            TimeSpan s1 = SessionStart.TimeOfDay;
            TimeSpan e1 = SessionEnd.TimeOfDay;

            if (s1 <= e1) return (now >= s1 && now <= e1);
            return (now >= s1 || now <= e1);
        }

        private bool CooldownWindowComplete(DateTime currentTime)
        {
            if (!UseCooldown) return true;
            if (lastExitTime == DateTime.MinValue) return true;
            return (currentTime - lastExitTime).TotalMinutes >= CooldownMinutes;
        }

        private bool CanSubmitLongEntry(DateTime currentTime)
        {
            if (Position.MarketPosition != MarketPosition.Flat)
                return false;

            if (dailyProfitHit)
                return false;

            if (!IsWithinActiveSession(currentTime))
                return false;

            if (!CooldownWindowComplete(currentTime))
                return false;

            return true;
        }

        private void PruneRecentBullStacks()
        {
            if (recentBullStacks == null || recentBullStacks.Count == 0)
                return;

            recentBullStacks.RemoveAll(s => CurrentBar - s.BarIndex > maxStackMemory);
        }

        private void PruneRecentBearStacks()
        {
            if (recentBearStacks == null || recentBearStacks.Count == 0)
                return;

            recentBearStacks.RemoveAll(s => CurrentBar - s.BarIndex > maxStackMemory);
        }

        private bool CanSubmitShortEntry(DateTime currentTime)
        {
            if (Position.MarketPosition != MarketPosition.Flat)
                return false;

            if (dailyProfitHit)
                return false;

            if (!IsWithinActiveSession(currentTime))
                return false;

            if (!CooldownWindowComplete(currentTime))
                return false;

            return true;
        }

        private bool TryUpdateDynamicStopLong(double desiredStopPrice)
        {
            if (Position.MarketPosition != MarketPosition.Long)
                return false;

            double roundedDesired = Instrument.MasterInstrument.RoundToTickSize(desiredStopPrice);

            double currentPrice = Close[0];
            if (State == State.Realtime)
            {
                double bid = GetCurrentBid();
                if (bid > 0) currentPrice = bid;
            }

            double maxValidStop = Instrument.MasterInstrument.RoundToTickSize(currentPrice - (SpreadCushionTicks * TickSize));

            if (roundedDesired <= currentStopPrice)
                return false;

            if (roundedDesired >= maxValidStop)
                return false;

            currentStopPrice = roundedDesired;
            SetStopLoss(CalculationMode.Price, currentStopPrice);
            return true;
        }

        private bool TryUpdateDynamicStopShort(double desiredStopPrice)
        {
            if (Position.MarketPosition != MarketPosition.Short)
                return false;

            double roundedDesired = Instrument.MasterInstrument.RoundToTickSize(desiredStopPrice);

            double currentPrice = Close[0];
            if (State == State.Realtime)
            {
                double ask = GetCurrentAsk();
                if (ask > 0) currentPrice = ask;
            }

            double minValidStop = Instrument.MasterInstrument.RoundToTickSize(currentPrice + (SpreadCushionTicks * TickSize));

            if (roundedDesired >= currentStopPrice)
                return false;

            if (roundedDesired <= minValidStop)
                return false;

            currentStopPrice = roundedDesired;
            SetStopLoss(CalculationMode.Price, currentStopPrice);
            return true;
        }

        private double CalculateCdSlopePct(NinjaTrader.NinjaScript.BarsTypes.VolumetricBarsType volBars, int lookback, int shift = 0)
        {
            if (lookback <= 0) return 0;
            if (CurrentBar - 1 - lookback - shift < 0) return 0;

            double rawCdSlope = 0;
            double sumVol = 0;

            for (int i = 0; i <= lookback; i++)
            {
                var vBar = volBars.Volumes[CurrentBar - 1 - shift - i];
                rawCdSlope += vBar.BarDelta;
                sumVol += vBar.TotalVolume;
            }

            if (sumVol == 0) return 0;
            return (rawCdSlope / sumVol) * 100.0;
        }
        #endregion

        #region Helper Methods - Bar Environment
        private bool IsRangeBarEnvironment()
        {
            try
            {
                return BarsPeriod != null && BarsPeriod.BarsPeriodType == BarsPeriodType.Range;
            }
            catch
            {
                return false;
            }
        }

        private double GetSignalClosePositionPct()
        {
            double range = High[1] - Low[1];
            if (range <= 0) return 0.5;
            return Math.Max(0.0, Math.Min(1.0, (Close[1] - Low[1]) / range));
        }

        private double GetSignalBodyPct()
        {
            double range = High[1] - Low[1];
            if (range <= 0) return 0.0;
            return Math.Abs(Close[1] - Open[1]) / range;
        }

        private double GetSignalUpperWickPct()
        {
            double range = High[1] - Low[1];
            if (range <= 0) return 0.0;
            return (High[1] - Math.Max(Open[1], Close[1])) / range;
        }

        private double GetSignalLowerWickPct()
        {
            double range = High[1] - Low[1];
            if (range <= 0) return 0.0;
            return (Math.Min(Open[1], Close[1]) - Low[1]) / range;
        }

        private double GetSignalOverlapPct()
        {
            if (CurrentBar < 3) return 0.0;
            double range = High[1] - Low[1];
            if (range <= 0) return 0.0;
            double overlapHigh = Math.Min(High[1], High[2]);
            double overlapLow  = Math.Max(Low[1], Low[2]);
            double overlap = Math.Max(0.0, overlapHigh - overlapLow);
            return Math.Max(0.0, Math.Min(1.0, overlap / range));
        }

        private string GetRangePaceLabel(double secs)
        {
            if (secs <= RangeFastBarSecsThreshold) return "FAST";
            if (secs >= RangeSlowBarSecsThreshold) return "SLOW";
            return "NORMAL";
        }
        #endregion

        #region Helper Methods - Logging
        private void PrintSettingsLog()
        {
            if (!UseTradeLogging) return;

            Print("=========================================================================");
            Print("SETTINGS LOG | MomentumSubsetEnhanced v2.53 (Tier 1 Revert)");
            Print("=========================================================================");

            Print(string.Format("[00]  DIRECTION      : Long={0} | Short={1}", AllowLongTrades, AllowShortTrades));
            Print(string.Format("[00b] REGIMES        : BullDiv={0} | BearDiv={1} | BullConv={2} | BearConv={3}", AllowBullDiv, AllowBearDiv, AllowBullConv, AllowBearConv));
            Print(string.Format("[01]  COOLDOWN       : Use={0} | Minutes={1}", UseCooldown, CooldownMinutes));
            Print(string.Format("[02]  IMBALANCE CORE : Ratio={0:F1} to {1:F1} | MinImbVol={2} | AllowInfEdge={3}", ImbalanceRatio, MaxImbalanceRatio, MinImbalanceVolume, AllowInfiniteEdgeRatio));
            Print(string.Format("[02b] GLOBAL-IMBALANCE-CORE : ResetAdaptDaily={0}", ResetAdaptiveOnDayTransition));

            Print("-------------------------------------------------------------------------");
            Print("[NEW GLOBAL FILTERS]");
            Print(string.Format("     VOL-REGIME GATE : Use={0} | Dead={1} | Quiet={2} | Normal={3} | Active={4} | Extreme={5}", 
                UseVolatilityRegimeGate, AllowDeadRegime, AllowQuietRegime, AllowNormalRegime, AllowActiveRegime, AllowExtremeRegime));
            Print(string.Format("     CLIMAX/EXHAUST  : UseClimax={0} (Block={1} | ReqPost={2}) | UseExhaust={3} (Req={4})",
                UseClimaxFilter, BlockEntryOnClimaxBar, RequirePostClimaxEntry, UseExhaustionFilter, RequireExhaustionSetup));
            Print(string.Format("     VALUE AREA      : Use={0} | NoVA={1} | BelVAL={2} | AtVAL={3} | InVal={4} | AtPOC={5} | AtVAH={6} | AbvVAH={7} | POCTouch={8} (Bars={9})",
                UseValueAreaFilter, VA_AllowNoVA, VA_AllowBelowVAL, VA_AllowAtVAL, VA_AllowInValue, VA_AllowAtPOC, VA_AllowAtVAH, VA_AllowAboveVAH, VA_RequirePOCTouch, VA_POCTouchLookbackBars));
            Print(string.Format("     SESSION CONTEXT : Use={0} | LowRev={1} | LowCont={2} | Mid={3} | UpCont={4} | HighBo={5}",
                UseSessionContextFilter, Session_AllowLowRev, Session_AllowLowerCont, Session_AllowMidRange, Session_AllowUpperCont, Session_AllowHighBo));
            Print(string.Format("     ADAPT MATRIX    : Use={0} | ConstVolAutoOff={1} | ShadowMode={2} | CeilingTrapAbs%={3:F1} | Pair/Family thresholds are internally calibrated by context and bar type",
                UseAdaptiveContextMatrix, AutoDisableBarVolumeFiltersOnConstantVolume, ShadowMatrixMode, AdaptiveCeilingTrapAbsorptionPct));
            Print(string.Format("     RANGE BAR ADAPT : Use={0} | Fast<={1:F0}s | Slow>={2:F0}s | ContClose>={3:P0} | SlowClose>={4:P0} | MaxOverlap<={5:P0} | RejWick>={6:P0}",
                UseRangeBarAdaptation, RangeFastBarSecsThreshold, RangeSlowBarSecsThreshold, RangeContinuationCloseMinPct, RangeStrongSlowBarCloseMinPct, RangeMaxOverlapPct, RangeMinRejectionWickPct));
            Print(string.Format("     DELTA VELOCITY  : Use={0} | Lookback={1} | MinROC={2:F1} | ReqAccel={3} | BlockAccelSell={4}",
                UseDeltaVelocityFilter, DeltaVelocityLookback, DV_MinDeltaROC, DV_RequirePositiveAccel, DV_BlockAcceleratingSelling));
            Print(string.Format("     ADAPT/PERF GATE : AdaptVol={0} (MinMult={1:F2} | MaxStd={2:F2}) | TimeAdj={3} (MinMult={4:F2}) | FollowThru={5} (Rate={6:P0} | MinSamples={7} | MinMFE={8:F1}T)",
                UseAdaptiveVolumeGate, AdaptiveVolumeMinMultiplier, AdaptiveVolumeMaxStdDevMultiplier,
                UseTimeAdjustedVolumeGate, TimeAdjustedVolumeMinMultiplier,
                UseFollowThroughGate, FollowThroughMinRate, FollowThroughMinSamples, FollowThroughMinTicks));
            Print(string.Format("     AVWAP ENGINE    : Use={0} | Anchor={1} | Deadzone={2}T | Extreme={3}T | Killzone={4}T",
                UseAvwapFilter, AvwapAnchor, AvwapDeadzoneTicks, AvwapExtremeTicks, AvwapKillzoneTicks));
            Print(string.Format("     AVWAP ADD-ONS   : SlopeVeto={0} (Lookback={1} | MinDrop={2}T) | AcceptanceFilter(Per-Anchor Confirmed Reclaim)={3}",
                UseAvwapSlopeFilter, AvwapSlopeLookbackBars, AvwapSlopeVetoTicks, UseVwapAcceptanceFilter));
            Print(string.Format("     KEY LEVELS      : Gate={0} | Prox={1}T | VWAP={2} PDH={3} PDL={4} IBH={5} IBL={6} PMH={7} PML={8} POC={9} | DeltaAgree={10} | RevAbsorb={11} | AvoidMidday={12}",
                UseKeyLevelGate, KeyLevelProximityTicks, KL_AllowVWAP, KL_AllowPDH, KL_AllowPDL, KL_AllowIBH, KL_AllowIBL, KL_AllowPMH, KL_AllowPML, KL_AllowPOC,
                KL_RequireDeltaAgreement, KL_RequireAbsorptionForReversal, KL_AvoidMiddayChop));
            Print(string.Format("     SPREAD TELEMETRY: Enabled (SignalSpread logged per trade; BookDepth pending OnMarketDepth() integration)"));
            Print(string.Format("     BAR-REGIME TEL  : Enabled (per-bar R1k+VolZ logged on every RTH bar for regime calibration)"));
            Print(string.Format("     MICRO-REGIME    : Enable={0} | Lookback={1} | Dense<{2:F1} | Thin>{3:F1} | AllowDense={4} | AllowNormal={5} | AllowThin={6} | AllowWarmup={7}",
                EnableRegimeFilter, R1kRollingWindowBars, RegimeDenseThreshold, RegimeThinThreshold, AllowDenseRegime, AllowNormalMicroRegime, AllowThinRegime, AllowWarmupRegime));
            Print(string.Format("     ADAPTIVE-40-RANGE: Use={0} | LowerCont+AccelBuy={1} | MidRange+AccelBuy={2} | NIC=1={3}",
                UseAdaptive40RangeFilter, Block_LowerCont_AccelBuy, Block_MidRange_AccelBuy, Block_NIC1));
            Print(string.Format("     ES-8-RANGE: Use={0} | HighBO+AccelBuy={1} | UpperFric+Quiet+AccelBuy={2} | AvwapExtreme={3}",
                UseESRangeFilter, ES_Block_HighBO_AccelBuy, ES_Block_UpperFriction_Quiet_AccelBuy, ES_Block_AvwapExtreme));
            Print(string.Format("     PHASE1-RULES: BlockSessLowRev={0} | BlockCeilingActiveAboveVAH={1} | BlockLowerContBelowValLowVol={2} | BlockCeilingAtVAH={3} | BlockLowerContCluster2={4}",
                BlockSessLowRev, BlockCeilingActiveAboveVAH, BlockLowerContBelowValLowVol, BlockCeilingAtVAH, BlockLowerContCluster2));

            Print("-------------------------------------------------------------------------");
            Print(string.Format("[04] TIER A PROFILE  : ENABLED = {0} | Target Size: {1} to {2}", S3_Enable, S3_MinStackSize, S3_MaxStackSize));
            Print(string.Format("     Bull Count      : Use={0} (Min={1} / Max={2})", S3_UseBullCount, S3_MinBullCount, S3_MaxBullCount));
            Print(string.Format("     Flow & CD       : UseSlope={0} ({1:F1}% to {2:F1}%) | CDAccel={3} (Min={4:F1} Shift={5})", S3_UseCdSlope, S3_MinCdSlope, S3_MaxCdSlope, S3_UseCdSlopeAccel, S3_MinCdSlopeAccel, S3_CdSlopeAccelShift));

            string rDiv3 = S3_RequireDivergence ? "True (Forces BULL-DIV)" : "False";
            Print(string.Format("     Delta & Regime  : ReqDiv={0} | DeltaDiv={1} (ReqDecel={2})", rDiv3, S3_UseDeltaDivergence, S3_RequireDeceleration));

            Print(string.Format("     Volume Limits   : UseMinVol={0} ({1}) | UseMaxVol={2} ({3}) | UseMaxImbVol={4} ({5:F1})", S3_UseMinVolume, S3_MinVolume, S3_UseMaxVolume, S3_MaxVolume, S3_UseMaxImbVol, S3_MaxImbVol));
            Print(string.Format("     Vol Spike       : Use={0} (Lookback={1} | Min={2:F2}x | Max={3:F2}x)", S3_UseVolumeSpike, S3_VolumeSpikeLookback, S3_MinVolumeSpikeRatio, S3_MaxVolumeSpikeRatio));
            Print(string.Format("     Dominance       : UseDom={0} (Cnt={1} / Dlt={2:F1}) | UseMinDomVol={3} ({4:F1}%) | UseMaxDomVol={5} ({6:F1}%)", S3_UseDominance, S3_MinDomCount, S3_MinDomDelta, S3_UseMinDomVol, S3_MinDomVol, S3_UseMaxDomVol, S3_MaxDomVol));
            
            Print(string.Format("     Bar Qual/Delta  : RawUse={0} (Min={1:F0} / Max={2:F0}) | NormUse={3} (Min={4:F1}% / Max={5:F1}%)", S3_UseBarDelta, S3_MinBarDelta, S3_MaxBarDelta, S3_UseNormalizedDelta, S3_MinNormalizedDeltaPct, S3_MaxNormalizedDeltaPct));
            
            Print(string.Format("     Opp Stack       : UseMin={0} ({1}) | UseMax={2} ({3})", S3_UseMinOppStack, S3_MinOppStack, S3_UseMaxOppStack, S3_MaxOppStack));
            Print(string.Format("     Footprint & POC : UseMinPoc={0} (Min={1:F2}) | UseMaxPoc={2} (Max={3:F2}) | PocMig={4} (ReqRev={5}) | UseMinEsc={6} ({7}T) | UseMaxEsc={8} ({9}T)", S3_UseMinPoc, S3_MinPoc, S3_UsePoc, S3_MaxPoc, S3_UsePocMigration, S3_RequirePocReversal, S3_UseMinEscape, S3_MinEscape, S3_UseMaxEscape, S3_MaxEscape));
            Print(string.Format("     Absorption      : Use={0} | MinPct={1:F1}% | UseMax={2} (MaxPct={3:F1}%) | ZoneTicks={4} | MinMult={5:F1}x", S3_UseAbsorption, S3_MinAbsorptionPct, S3_UseMaxAbsorption, S3_MaxAbsorptionPct, S3_AbsorptionZoneTicks, S3_MinAbsorptionMultiple));
            Print(string.Format("     Recency         : Use={0} (Min={1:F2} / Max={2:F2})", S3_UseRecency, S3_MinRecency, S3_MaxRecency));
            Print("-------------------------------------------------------------------------");
            Print(string.Format("[05] RISK MANAGEMENT : Stop={0}T | Target={1}T | BE={2} ({3}T) | Trail={4} | MaxDaily={5} (${6}) | ShadowDaily={7} (${8})", 
                StopLossTicks, TakeProfitTicks, UseBreakEven, BreakEvenTriggerTicks, UseAutoTrail, UseMaxDailyProfit, MaxDailyProfit, UseShadowDailyProfitTracker, ShadowDailyProfitTarget));
            Print("=========================================================================");
        }

        private void PrintDailySummary()
        {
            if (!UseTradeLogging || dailyTradeCount == 0) return;

            Print("=========================================================================");
            Print(string.Format("DAILY SUMMARY | {0} | Trades: {1} | Wins: {2} | Losses: {3} | PnL: {4:F0} Ticks",
                currentTradingDay.ToString("yyyy-MM-dd"), dailyTradeCount, dailyWins, dailyLosses, dailyPnlTicks));
            Print("-------------------------------------------------------------------------");

            Print("[CONTEXT BREAKDOWN]");
            foreach (var ctx in dailyContextCounts.Keys)
            {
                double avgPnl = dailyContextCounts[ctx] > 0 ? dailyContextPnl[ctx] / dailyContextCounts[ctx] : 0;
                Print(string.Format("     {0}: {1} trades | Total: {2:F0}T | Avg: {3:F1}T",
                    ctx, dailyContextCounts[ctx], dailyContextPnl[ctx], avgPnl));
            }

            Print("[VOLATILITY REGIME BREAKDOWN]");
            foreach (var reg in dailyRegimeCounts.Keys)
            {
                double avgPnl = dailyRegimeCounts[reg] > 0 ? dailyRegimePnl[reg] / dailyRegimeCounts[reg] : 0;
                Print(string.Format("     {0}: {1} trades | Total: {2:F0}T | Avg: {3:F1}T",
                    reg, dailyRegimeCounts[reg], dailyRegimePnl[reg], avgPnl));
            }

            Print("[CLUSTER BREAKDOWN]");
            foreach (var key in dailyClusterCounts.Keys)
            {
                double avgPnl = dailyClusterCounts[key] > 0 ? dailyClusterPnl[key] / dailyClusterCounts[key] : 0;
                Print(string.Format("     {0}: {1} trades | Total: {2:F0}T | Avg: {3:F1}T",
                    key, dailyClusterCounts[key], dailyClusterPnl[key], avgPnl));
            }

            double ftRate, ftAvgMfe, ftAvgMae;
            int ftSampleCount;
            GetFollowThroughStats(out ftRate, out ftAvgMfe, out ftAvgMae, out ftSampleCount);
            Print(string.Format("[FOLLOW-THROUGH] Rate: {0:P0} | AvgMFE: {1:F1}T | AvgMAE: {2:F1}T | Samples: {3}",
                ftRate, ftAvgMfe, ftAvgMae, ftSampleCount));
                
            if (UseShadowDailyProfitTracker)
            {
                Print(string.Format("[SHADOW PROFIT TARGET] Target: ${0:F2} | Reached: {1}", 
                    ShadowDailyProfitTarget, shadowProfitHit ? "YES" : "NO"));
            }

            Print("=========================================================================");
        }

        private void PrintTradeLog(Trade lastTrade)
        {
            double pTicks = lastTrade.ProfitPoints / TickSize;
            double pDollars = lastTrade.ProfitCurrency;
            double mTicks = lastTrade.MaePoints / TickSize;
            double fTicks = lastTrade.MfePoints / TickSize;
            string rOut = pTicks > 0 ? "WIN" : (pTicks < 0 ? "LOSS" : "BE");

            if (lastTrade.Exit != null && !string.IsNullOrEmpty(lastTrade.Exit.Name))
            {
                if (lastTrade.Exit.Name.StartsWith("Exit") || lastTrade.Exit.Name.StartsWith("Abort"))
                    rOut = lastTrade.Exit.Name.ToUpper();
            }

            bool passAdaptVolMin = lastEntryTotalBarVol >= lastEntryAdaptiveMinVol;
            bool passAdaptVolMax = lastEntryTotalBarVol <= lastEntryAdaptiveMaxVol;
            bool passAdaptiveVolumeGate = !UseAdaptiveVolumeGate || (passAdaptVolMin && passAdaptVolMax);
            bool passTimeAdj = lastEntryTotalBarVol >= lastEntryTimeAdjMinVol;
            bool passTimeAdjustedGate = !UseTimeAdjustedVolumeGate || passTimeAdj;
            bool passFt = lastEntryFollowThroughRate >= FollowThroughMinRate || lastEntryFtSampleCount < FollowThroughMinSamples;
            bool passFollowThroughGate = !UseFollowThroughGate || passFt;
            bool passRegime = lastEntryVolRegimeGateAllowed;

            Print(""); 
            Print(string.Format("TRADE LOG | RESULT: {0} ({1} Ticks / ${2:F2}) | MAE: {3} Ticks | MFE: {4} Ticks | ENTRY: {5}", 
                rOut, Math.Round(pTicks), pDollars, Math.Round(mTicks), Math.Round(fTicks), pendingTradeLog));

            Print(string.Format("     [ENTRY-SNAPSHOT] Context: {0} | SessionAxis: {1} | VolRegime: {2} | Recency: {3:F2} | SessPos: {4:F2} | VolZ: {5:F2} | Cluster: {6}",
                lastEntryContext, lastEntrySessionAxis, lastEntryVolRegime, lastEntryStackRecency, lastEntrySessionPos, lastEntryVolZScore, lastEntryClusterCount));

            Print(string.Format("     [LOCATION-RAW] SigPx: {0:F2} | SessLow: {1:F2} ({2}) | SessMid: {3:F2} ({4}) | SessHigh: {5:F2} ({6}) | Bucket: {7} | SessionCtx: {8} | VAContext: {9} | Pair: {10}",
                lastEntrySignalPrice,
                lastEntrySessionLow, FormatSignedTicks(lastEntryPriceToSessionLowTicks),
                lastEntrySessionMid, FormatSignedTicks(lastEntryPriceToSessionMidTicks),
                lastEntrySessionHigh, FormatSignedTicks(lastEntryPriceToSessionHighTicks),
                string.IsNullOrEmpty(lastEntrySessionAxis) ? GetLocationBucketLabel(lastEntrySessionPos) : lastEntrySessionAxis, lastEntryContext, lastEntryVAContext, lastEntrySpatialPair));

            Print(string.Format("     [LOCATION-VA] VAL: {0:F2} ({1}) | POC: {2:F2} ({3}) | VAH: {4:F2} ({5}) | ActiveAVWAP: {6} | ActiveDist(C1): {7}",
                lastEntryVAL, FormatSignedTicks(lastEntryPriceToVALTicks),
                lastEntrySessionPOCVA, FormatSignedTicks(lastEntryPriceToPOCSignedTicks),
                lastEntryVAH, FormatSignedTicks(lastEntryPriceToVAHTicks),
                string.IsNullOrEmpty(lastEntryAvwapActiveAnchor) ? "N/A" : lastEntryAvwapActiveAnchor,
                FormatSignedTicks(-lastEntryAvwapSignalDistTicks)));

            Print(string.Format("     [KEY-LEVELS] Nearest: {0} ({1:F1}T) | GatePass: {2} | Summary: {3}",
                lastEntryNearestKeyLevel, lastEntryNearestKeyLevelDistTicks, lastEntryKeyLevelGatePass, lastEntryKeyLevelSummary));
            Print(string.Format("     [KEY-LEVEL-FLAGS] VWAP={0} PDH={1} PDL={2} IBH={3} IBL={4} PMH={5} PML={6} POC={7}",
                lastEntryNearVWAP, lastEntryNearPDH, lastEntryNearPDL, lastEntryNearIBH, lastEntryNearIBL, lastEntryNearPMH, lastEntryNearPML, lastEntryNearPOC));

            Print(string.Format("     [LIQUIDITY-RAW] Range: {0:F1}T | Secs: {1:F2} | R/1k: {2:F1}T | BarDelta: {3:F0} | Delta/Tick: {4:F1} | Delta/Vol: {5:F1}% | Escape: {6:F1}T | DomVol: {7:F1}% | Ratio: {8:F1}",
                lastEntrySignalBarRangeTicks, lastEntrySignalBarSecs, lastEntryRangePer1kVolumeTicks, lastEntryBarDelta, lastEntryDeltaPerTick, lastEntryDeltaPctOfVolume,
                lastEntryEscapeTicks, lastEntryDomVolPercent, lastEntryValidBullishRatio));
            Print(string.Format("     [SPREAD-DEPTH] SignalSpread: {0:F1}T | AvgSpread: {1:F1}T | MaxSpread: {2:F1}T | BidVol: {3:F0} | AskVol: {4:F0}",
                lastEntrySignalSpread,
                lastEntryAvgSpread,
                lastEntryMaxSpread,
                lastEntryBookBidVol,
                lastEntryBookAskVol));

            if (lastEntryRangeBarMode)
                Print(string.Format("     [RANGE-BAR] Pace: {0} | ClosePos: {1:P0} | Body: {2:P0} | Overlap: {3:P0} | LowWick: {4:P0} | UpWick: {5:P0}",
                    lastEntryRangePace, lastEntryRangeClosePos, lastEntryRangeBodyPct, lastEntryRangeOverlapPct, lastEntryRangeLowerWickPct, lastEntryRangeUpperWickPct));

            Print(string.Format("     [FOOTPRINT-RAW] ImbCount: {0}B/{1}S | ImbDensity: {2:F2}/T | Stack: {3} vs Opp: {4} | POCPos: {5:F2} | POCVol: {6:F0} ({7:F1}%) | LowZone: {8:F0} ({9:F1}%) | UpperZone: {10:F0} ({11:F1}%)",
                lastEntryBullishImbalanceCount, lastEntryBearishImbalanceCount, lastEntryImbalanceDensity, lastEntryMaxBullishStack, lastEntryMaxBearishStack,
                lastEntryPocPosition, lastEntryMaxVolAtPrice, lastEntryPocVolPct, lastEntryLowZoneVol, lastEntryLowZonePct, lastEntryUpperZoneVol, lastEntryUpperZonePct));

            Print(string.Format("     [MATRIX-PROFILE] Family: {0} | Pair: {1} | ConstVolMode: {2} | DisableBarVolFilters: {3} | RuleSet: {4}",
                lastEntryAdaptiveFamily, lastEntrySpatialPair, lastEntryConstantVolumeMode, lastEntryDisableBarVolumeFilters, lastEntryAdaptiveRuleSummary));

            Print(string.Format("     [MATRIX-STATE] BaseStack: {0} | PreMatrix: {1} | Matrix: {2} | Proofs: {3} | VerdictReason: {4}",
                lastEntryBaseStackPass, lastEntryPreMatrixPass, lastEntryMatrixVerdict, lastEntryMatrixProofState, lastEntryMatrixBlockReason));

            if (ShadowMatrixMode)
            {
                Print("     [SHADOW] BaseStack (Raw Footprint): " + (lastEntryBaseStackPass ? "PASS" : "BLOCK"));
                Print("     [SHADOW] Pre-Matrix (AVWAP/Global Filters): " + (lastEntryPreMatrixPass ? "PASS" : "BLOCK"));
                Print("     [SHADOW] Matrix Only (Context Engine): " + (lastEntryMatrixVerdict ? "PASS" : "BLOCK"));
                Print("     [SHADOW] Full Engine Verdict: " + ((lastEntryPreMatrixPass && lastEntryMatrixVerdict) ? "PASS" : "BLOCK"));
            }

            Print(string.Format("     [ENTRY-ADAPTIVE] Vol: {0:F0} | Base: {1:F0} | StdDev: {2:F0} | Min/Max: {3:F0}/{4:F0} | GateEnabled: {5} | PassMin: {6} | PassMax: {7} | PassGate: {8} | PassRegime: {9} | Spike: {10:F2}x",
                lastEntryTotalBarVol, lastEntryAdaptiveVolBase, lastEntryAdaptiveVolStdDev, lastEntryAdaptiveMinVol, lastEntryAdaptiveMaxVol, UseAdaptiveVolumeGate, passAdaptVolMin, passAdaptVolMax, passAdaptiveVolumeGate, passRegime, lastEntryVolumeSpikeRatio));

            Print(string.Format("     [ENTRY-TIME&FT] TimeAdjMin: {0:F0} | TimeGate={1} (Pass: {2}) | FTRate: {3:P0} | FTGate={4} (Pass: {5}) | AvgMFE: {6:F1}T | AvgMAE: {7:F1}T | Samples: {8}",
                lastEntryTimeAdjMinVol, UseTimeAdjustedVolumeGate, passTimeAdjustedGate, lastEntryFollowThroughRate, UseFollowThroughGate, passFollowThroughGate, lastEntryAvgMfe, lastEntryFtAvgMae, lastEntryFtSampleCount));

            Print(string.Format("     [VOL-REGIME] Regime: {0} | ZScore: {1:F2} | GateEnabled: {2} | GateAllowed: {3}",
                lastEntryVolRegime, lastEntryVolZScore, UseVolatilityRegimeGate, lastEntryVolRegimeGateAllowed));

            Print(string.Format("     [REGIME] RollR1k={0:F1} | Regime={1} | Thresholds={2:F1}/{3:F1}",
                lastEntryRollingR1k, lastEntryMicroRegime, RegimeDenseThreshold, RegimeThinThreshold));

            Print(string.Format("     [ADAPTIVE-40-RANGE] Enabled={0} | Pass={1} | Regime={2} | Context={3} | Momentum={4}",
                UseAdaptive40RangeFilter, lastEntryAdaptive40RangeFilterPass, lastEntryMicroRegime, lastEntryContext, lastEntryDeltaMomentum));

            Print(string.Format("     [ES-8-RANGE] Enabled={0} | Pass={1} | Context={2} | Momentum={3} | Family={4} | VolRegime={5} | AvwapTier={6}",
                UseESRangeFilter, lastEntryESRangeFilterPass, lastEntryContext, lastEntryDeltaMomentum, lastEntryAdaptiveFamily, lastEntryVolRegime, lastEntryAvwapTier));

            Print(string.Format("     [CLIMAX-EXHAUST] IsClimax: {0} | PrevClimax: {1} | IsExhaust: {2} | ClimaxScore: {3:F2} | ExhaustScore: {4:F2} | PrevVol: {5:F0} | CurVol: {6:F0} | PassClimax: {7} | PassExhaust: {8}",
                lastEntryBarIsClimax, lastEntryPrevBarWasClimax, lastEntryBarIsExhaustion, lastEntryClimaxScore, lastEntryExhaustionScore,
                lastEntryClimaxPrevVol, lastEntryClimaxCurVol, lastEntryPassClimaxFilter, lastEntryPassExhaustionFilter));

            Print(string.Format("     [VALUE-AREA] VAH: {0:F2} | VAL: {1:F2} | POC: {2:F2} | Context: {3} | DistToPOC: {4:F1}T | FilterEnabled: {5} | Pass: {6}",
                lastEntryVAH, lastEntryVAL, lastEntrySessionPOCVA, lastEntryVAContext, lastEntryPriceDistToPOC, UseValueAreaFilter, lastEntryPassVAFilter));

            Print(string.Format("     [DELTA-VELOCITY] ROC: {0:F1} | Accel: {1:F1} | Score: {2:F2} | Momentum: {3} | FilterEnabled: {4} | Pass: {5}",
                lastEntryDeltaROC, lastEntryDeltaAccel, lastEntryDeltaVelocityScore, lastEntryDeltaMomentum, UseDeltaVelocityFilter, lastEntryPassDeltaVelocityFilter));

            Print(string.Format("     [CD-ACCEL] Accel: {0:F1}% | OldSlope: {1:F1}% | Pass: {2}",
                lastEntrySlopeAccel, lastEntryOlderSlope, lastEntryPassCdAccel));

            Print(string.Format("     [DELTA-DIV] Dir: {0} | NormDelta: {1:F1}% | RawCur: {2:F0} | Prev1: {3:F0} | Prev2: {4:F0} | Div: {5} | Decel: {6} | Pass: {7}",
                lastEntryBarDir, lastEntryNormDeltaPct, lastEntryBarDelta, lastEntryPrevBarDelta1, lastEntryPrevBarDelta2, lastEntryDivLong, lastEntryImprovingDelta, lastEntryPassDeltaDiv));

            Print(string.Format("     [ABSORB] Vol: {0:F0} ({1:F1}%) | Bid: {2:F0} | Ask: {3:F0} | Mult: {4:F1}x | Pass: {5}",
                lastEntryLowZoneVol, lastEntryAbsPct, lastEntryLowBid, lastEntryLowAsk, lastEntryAbsMult, lastEntryPassAbsorb));

            Print(string.Format("     [POC-MIG] Cur: {0:F2} | Prev1: {1:F2} | Prev2: {2:F2} | MigTicks: {3:F1} | RevUp: {4} | Pass: {5}",
                lastEntryCurrentPoc, lastEntryPrevPoc1, lastEntryPrevPoc2, lastEntryPocMig1, lastEntryRevUp, lastEntryPassPocMig));

            Print(string.Format("     [AVWAP-DECISION] ActiveAnchor: {0} | Tier: {1} | Slope: {2} (Drop: {3:F1}T) | SignalDistBelow(C1): {4:F1}T | Reclaimed: {5}",
                string.IsNullOrEmpty(lastEntryAvwapActiveAnchor) ? "N/A" : lastEntryAvwapActiveAnchor,
                lastEntryAvwapTier, lastEntryAvwapSlope, lastEntryAvwapSlopeDropTicks, lastEntryAvwapSignalDistTicks, lastEntryAvwapReclaimed));

            // Output AVWAP Shadow Telemetry
            double fillPx = lastTrade.Entry.Price;

            if (lastEntryAvwapOpen > 0)
            {
                double fillDistRaw = (fillPx - lastEntryAvwapOpen) / TickSize;
                Print(string.Format("     [AVWAP-TEST] Anchor: OPEN | Live: {0:F2} | Hist: {1:F2} | C1: {2:F2} | Entry: {3:F2} | SignalDistBelow(C1): {4:F1}T | FillDistSigned: {5}{6:F1}T | FillPos: {7} | ZONE: {8} | SLOPE: {9} (Drop: {10:F1}T) | RECLAIMED: {11}", 
                    lastEntryAvwapOpen, lastEntryAvwapOpenHistorical, Close[1], fillPx, lastEntryAvwapOpenSignalDistTicks,
                    fillDistRaw >= 0 ? "+" : "", fillDistRaw, fillPx >= lastEntryAvwapOpen ? "ABOVE" : "BELOW",
                    lastEntryAvwapOpenTier, lastEntryAvwapOpenSlope, lastEntryAvwapOpenSlopeDropTicks, lastEntryAvwapOpenReclaimed));
            }
            if (lastEntryAvwapHigh > 0)
            {
                double fillDistRaw = (fillPx - lastEntryAvwapHigh) / TickSize;
                Print(string.Format("     [AVWAP-TEST] Anchor: HIGH | Live: {0:F2} | Hist: {1:F2} | C1: {2:F2} | Entry: {3:F2} | SignalDistBelow(C1): {4:F1}T | FillDistSigned: {5}{6:F1}T | FillPos: {7} | ZONE: {8} | SLOPE: {9} (Drop: {10:F1}T) | RECLAIMED: {11}", 
                    lastEntryAvwapHigh, lastEntryAvwapHighHistorical, Close[1], fillPx, lastEntryAvwapHighSignalDistTicks,
                    fillDistRaw >= 0 ? "+" : "", fillDistRaw, fillPx >= lastEntryAvwapHigh ? "ABOVE" : "BELOW",
                    lastEntryAvwapHighTier, lastEntryAvwapHighSlope, lastEntryAvwapHighSlopeDropTicks, lastEntryAvwapHighReclaimed));
            }
            if (lastEntryAvwapLow > 0)
            {
                double fillDistRaw = (fillPx - lastEntryAvwapLow) / TickSize;
                Print(string.Format("     [AVWAP-TEST] Anchor: LOW  | Live: {0:F2} | Hist: {1:F2} | C1: {2:F2} | Entry: {3:F2} | SignalDistBelow(C1): {4:F1}T | FillDistSigned: {5}{6:F1}T | FillPos: {7} | ZONE: {8} | SLOPE: {9} (Drop: {10:F1}T) | RECLAIMED: {11}", 
                    lastEntryAvwapLow, lastEntryAvwapLowHistorical, Close[1], fillPx, lastEntryAvwapLowSignalDistTicks,
                    fillDistRaw >= 0 ? "+" : "", fillDistRaw, fillPx >= lastEntryAvwapLow ? "ABOVE" : "BELOW",
                    lastEntryAvwapLowTier, lastEntryAvwapLowSlope, lastEntryAvwapLowSlopeDropTicks, lastEntryAvwapLowReclaimed));
            }

            double holdSeconds = (lastTrade.Entry != null && lastTrade.Exit != null) ? (lastTrade.Exit.Time - lastTrade.Entry.Time).TotalSeconds : 0;
            string exitName = (lastTrade.Exit != null && !string.IsNullOrEmpty(lastTrade.Exit.Name)) ? lastTrade.Exit.Name : "N/A";
            Print(string.Format("     [EXIT-MGMT] HoldSecs: {0:F1} | ExitName: {1} | BETriggered: {2} | TrailTriggered: {3} | MaxTrailStep: {4} | FinalStop: {5:F2} | PeakPx: {6:F2}",
                holdSeconds, exitName, lastClosedTradeBreakEvenTriggered, lastClosedTradeTrailTriggered, lastClosedTradeMaxTrailStep, lastClosedTradeFinalStopPrice, lastClosedTradeHighestSeenPrice));

            Print("=========================================================================");
        }
        #endregion

        #region Event Handlers
        protected override void OnExecutionUpdate(Execution execution, string executionId, double price, int quantity, MarketPosition marketPosition, string orderId, DateTime time)
        {
            _lastExecutionTime = time;
        }

        protected override void OnPositionUpdate(Position position, double averagePrice, int quantity, MarketPosition marketPosition)
        {
            if (position == null || position.Instrument == null || position.Instrument.FullName != Instrument.FullName)
                return;

            if (marketPosition == MarketPosition.Flat)
            {
                lastExitTime = _lastExecutionTime != DateTime.MinValue ? _lastExecutionTime : Time[0];
                lastClosedTradeBreakEvenTriggered = breakEvenTriggered;
                lastClosedTradeTrailTriggered = lastTrailStep >= 0;
                lastClosedTradeMaxTrailStep = lastTrailStep;
                lastClosedTradeFinalStopPrice = currentStopPrice;
                lastClosedTradeHighestSeenPrice = highestSeenPrice;
                ResetTradeManagementState();
                SetStopLoss(CalculationMode.Ticks, StopLossTicks);
            }
            else if (marketPosition == MarketPosition.Long)
            {
                highestSeenPrice = averagePrice;
                currentStopPrice = averagePrice - (StopLossTicks * TickSize);
            }
            else if (marketPosition == MarketPosition.Short)
            {
                lowestSeenPrice = averagePrice;
                currentStopPrice = averagePrice + (StopLossTicks * TickSize);
            }
        }

        protected override void OnMarketData(MarketDataEventArgs marketDataUpdate)
        {
            if (marketDataUpdate.MarketDataType == MarketDataType.Ask || marketDataUpdate.MarketDataType == MarketDataType.Bid)
            {
                double bid = GetCurrentBid();
                double ask = GetCurrentAsk();
                if (bid > 0 && ask > 0 && ask > bid)
                {
                    double spread = (ask - bid) / TickSize;
                    barSpreadSum += spread;
                    barSpreadCount++;
                    if (spread > barSpreadMax) barSpreadMax = spread;
                    if (spread < barSpreadMin) barSpreadMin = spread;
                }
            }
        }
        #endregion
        
        #region OnBarUpdate
        protected override void OnBarUpdate()
        {
            #region Early Exit Checks
            if (CurrentBars[0] < BarsRequiredToTrade) return;
            if (BarsInProgress != 0) return;

            var vBarsType = BarsArray[0].BarsType as NinjaTrader.NinjaScript.BarsTypes.VolumetricBarsType;
            if (vBarsType == null) return;
            if (CurrentBar < 1) return;
            #endregion

            #region Settings Log (One-Time)
            if (!hasPrintedSettings)
            {
                PrintSettingsLog();
                hasPrintedSettings = true;
            }
            #endregion

            #region RTH Open & VWAP Acceptance Tracking
            // Confirmed-bar reclaim only: each anchor tracks its own acceptance state.
            if (IsFirstTickOfBar)
            {
                hasReclaimedOpenVwap = UpdateAnchorReclaimState(vBarsType, rthOpenBarIdx, hasReclaimedOpenVwap);
                hasReclaimedHighVwap = UpdateAnchorReclaimState(vBarsType, sessionHighBarIdx, hasReclaimedHighVwap);
                hasReclaimedLowVwap  = UpdateAnchorReclaimState(vBarsType, sessionLowBarIdx, hasReclaimedLowVwap);
            }
            #endregion

            #region Process Completed Trades
            if (SystemPerformance.AllTrades.Count > lastTradeCount)
            {
                int newTradeCount = SystemPerformance.AllTrades.Count;

                for (int i = lastTradeCount; i < newTradeCount; i++)
                {
                    Trade processedTrade = SystemPerformance.AllTrades[i];
                    RecordTradeResult(processedTrade, lastEntryContext, lastEntryVolRegime, lastEntryStackRecency, lastEntryClusterCount);

                    if (UseTradeLogging && !string.IsNullOrEmpty(pendingTradeLog) && i == newTradeCount - 1)
                    {
                        PrintTradeLog(processedTrade);
                    }
                }

                lastTradeCount = newTradeCount;
                pendingTradeLog = "";
            }
            #endregion

            #region Live Bar Data Access
            var liveVBar = vBarsType.Volumes[CurrentBar];
            if (liveVBar == null) return;

            #endregion

            #region Session Exit Check
            if (Position.MarketPosition != MarketPosition.Flat)
            {
                if (!IsWithinActiveSession(Time[0]))
                {
                    if (Position.MarketPosition == MarketPosition.Long)
                        ExitLong("Exit-Session", "");
                    else if (Position.MarketPosition == MarketPosition.Short)
                        ExitShort("Exit-Session", "");
                    return;
                }
            }
            #endregion

            #region Daily Profit Check
            // Core Hard Exit Logic
            if (UseMaxDailyProfit && !dailyProfitHit)
            {
                double currentDayPnL = SystemPerformance.AllTrades.TradesPerformance.Currency.CumProfit - sessionStartProfit;
                if (Position.MarketPosition != MarketPosition.Flat)
                {
                    currentDayPnL += Position.GetUnrealizedProfitLoss(PerformanceUnit.Currency, Close[0]);
                }

                if (currentDayPnL >= MaxDailyProfit)
                {
                    dailyProfitHit = true;
                    if (Position.MarketPosition == MarketPosition.Long)
                    {
                        ExitLong("Exit-DailyMax", "");
                        return;
                    }
                    else if (Position.MarketPosition == MarketPosition.Short)
                    {
                        ExitShort("Exit-DailyMax", "");
                        return;
                    }
                }
            }

            // Shadow Telemetry Logic
            if (UseShadowDailyProfitTracker && !shadowProfitHit)
            {
                double currentDayPnL = SystemPerformance.AllTrades.TradesPerformance.Currency.CumProfit - sessionStartProfit;
                if (Position.MarketPosition != MarketPosition.Flat)
                {
                    currentDayPnL += Position.GetUnrealizedProfitLoss(PerformanceUnit.Currency, Close[0]);
                }

                if (currentDayPnL >= ShadowDailyProfitTarget)
                {
                    shadowProfitHit = true;
                }
            }
            #endregion

            #region Position Management (Break-Even / Trailing Stop)
            if (Position.MarketPosition == MarketPosition.Long && !dailyProfitHit)
            {
                if (High[0] > highestSeenPrice)
                    highestSeenPrice = High[0];
                    
                double mfeTicks = (highestSeenPrice - Position.AveragePrice) / TickSize;

                // Break-Even Logic
                if (UseBreakEven && !breakEvenTriggered && mfeTicks >= BreakEvenTriggerTicks)
                {
                    double bePrice = Position.AveragePrice + (BreakEvenOffsetTicks * TickSize);

                    if (TryUpdateDynamicStopLong(bePrice))
                    {
                        breakEvenTriggered = true;

                        if (UseTradeLogging)
                            Print(string.Format("{0} | BE TRIGGERED | MFE: {1:F1}T | Stop moved to: {2}",
                                Time[0].ToString("HH:mm:ss"), mfeTicks, currentStopPrice));
                    }
                }

                // Trailing Stop Logic
                if (UseAutoTrail && mfeTicks >= AutoTrailTriggerTicks)
                {
                    int steps = (int)Math.Floor((mfeTicks - AutoTrailTriggerTicks) / AutoTrailFrequencyTicks);
                    if (steps > lastTrailStep)
                    {
                        double activeMfeLevelTicks = AutoTrailTriggerTicks + (steps * AutoTrailFrequencyTicks);
                        double newStopPrice = Position.AveragePrice + ((activeMfeLevelTicks - AutoTrailStopLossTicks) * TickSize);

                        if (TryUpdateDynamicStopLong(newStopPrice))
                        {
                            lastTrailStep = steps;

                            if (UseTradeLogging)
                                Print(string.Format("{0} | TRAIL STEP {1} | MFE: {2:F1}T | Stop moved to: {3}",
                                    Time[0].ToString("HH:mm:ss"), steps, mfeTicks, currentStopPrice));
                        }
                    }
                }
            }
            else if (Position.MarketPosition == MarketPosition.Short && !dailyProfitHit)
            {
                if (Low[0] < lowestSeenPrice)
                    lowestSeenPrice = Low[0];

                double mfeTicks = (Position.AveragePrice - lowestSeenPrice) / TickSize;

                // Break-Even Logic
                if (UseBreakEven && !breakEvenTriggered && mfeTicks >= BreakEvenTriggerTicks)
                {
                    double bePrice = Position.AveragePrice - (BreakEvenOffsetTicks * TickSize);

                    if (TryUpdateDynamicStopShort(bePrice))
                    {
                        breakEvenTriggered = true;

                        if (UseTradeLogging)
                            Print(string.Format("{0} | BE TRIGGERED (SHORT) | MFE: {1:F1}T | Stop moved to: {2}",
                                Time[0].ToString("HH:mm:ss"), mfeTicks, currentStopPrice));
                    }
                }

                // Trailing Stop Logic
                if (UseAutoTrail && mfeTicks >= AutoTrailTriggerTicks)
                {
                    int steps = (int)Math.Floor((mfeTicks - AutoTrailTriggerTicks) / AutoTrailFrequencyTicks);
                    if (steps > lastTrailStep)
                    {
                        double activeMfeLevelTicks = AutoTrailTriggerTicks + (steps * AutoTrailFrequencyTicks);
                        double newStopPrice = Position.AveragePrice - ((activeMfeLevelTicks - AutoTrailStopLossTicks) * TickSize);

                        if (TryUpdateDynamicStopShort(newStopPrice))
                        {
                            lastTrailStep = steps;

                            if (UseTradeLogging)
                                Print(string.Format("{0} | TRAIL STEP {1} (SHORT) | MFE: {2:F1}T | Stop moved to: {3}",
                                    Time[0].ToString("HH:mm:ss"), steps, mfeTicks, currentStopPrice));
                        }
                    }
                }
            }
            #endregion

            if (!IsFirstTickOfBar) return;

            // Reset bar-level spread tracking for the new bar
            barSpreadSum = 0;
            barSpreadMax = 0;
            barSpreadCount = 0;
            barSpreadMin = double.MaxValue;

            #region Adaptive Baseline Updates
            UpdateAdaptiveBaselines(vBarsType);
            #endregion

            #region Day Transition Handling
            DateTime thisTradingDay = sessionIterator.GetTradingDay(Time[0]);
            if (thisTradingDay != currentTradingDay)
            {
                if (currentTradingDay != DateTime.MinValue)
                {
                    PrintDailySummary();
                    ResetDailyStats();
                }

                currentTradingDay = thisTradingDay;
                sessionStartProfit = SystemPerformance.AllTrades.TradesPerformance.Currency.CumProfit;
                dailyProfitHit = false;
                shadowProfitHit = false;

                if (sessionInitialized)
                {
                    priorDayHigh = sessionHigh;
                    priorDayLow = sessionLow;
                }

                ResetSessionTracking();
                ResetKeyLevelTracking();
                
                if (ResetAdaptiveOnDayTransition)
                {
                    ResetAdaptiveBuffers();
                }
                
                // Reset NYSE Value Area for new day
                ResetNYSEValueArea();
                lastNYSESessionDate = thisTradingDay;
            }

            if (dailyProfitHit)
            {
                return;
            }

            if (!IsWithinActiveSession(Time[0]))
            {
                return;
            }
            #endregion

            #region Confirmed Session Tracking
            UpdateSessionTrackingConfirmedBar();
            UpdateKeyLevelTrackingConfirmedBar();
            #endregion

            #region Bar Direction Detection
            string barDir = "DOJI";
            if (Close[1] > Open[1]) barDir = "GREEN";
            else if (Close[1] < Open[1]) barDir = "RED";
            #endregion

            #region Confirmed Bar Data Extraction
            var confirmedBar = vBarsType.Volumes[CurrentBar - 1];
            double totalBarVol = confirmedBar.TotalVolume;
            double currentBarRange = High[1] - Low[1];

            // Historical Delta Values
            double barDelta = confirmedBar.BarDelta;
            double prevBarDelta1 = CurrentBar >= 3 ? vBarsType.Volumes[CurrentBar - 2].BarDelta : 0;
            double prevBarDelta2 = CurrentBar >= 4 ? vBarsType.Volumes[CurrentBar - 3].BarDelta : 0;

            // Volume Spike Ratio Calculation
            double recentVolSum = 0;
            int validSpikeLookback = Math.Min(S3_VolumeSpikeLookback, CurrentBar - 1);
            for(int i = 1; i <= validSpikeLookback; i++)
            {
                recentVolSum += vBarsType.Volumes[CurrentBar - 1 - i].TotalVolume;
            }
            double recentAvgVol = validSpikeLookback > 0 ? recentVolSum / validSpikeLookback : 0;
            double currentVolSpikeRatio = recentAvgVol > 0 ? totalBarVol / recentAvgVol : 1.0;
            #endregion

            #region Update NYSE Value Area
            int vaStartTick = Convert.ToInt32(Math.Round(Low[1] / TickSize));
            int vaEndTick = Convert.ToInt32(Math.Round(High[1] / TickSize));
            if (IsWithinNYSESession(Time[1]))
            {
                for (int t = vaStartTick; t <= vaEndTick; t++)
                {
                    double p = Instrument.MasterInstrument.RoundToTickSize(t * TickSize);
                    double askVol = confirmedBar.GetAskVolumeForPrice(p);
                    double bidVol = confirmedBar.GetBidVolumeForPrice(p);
                    double tickVol = askVol + bidVol;

                    if (tickVol > 0)
                        UpdateNYSEValueArea(p, tickVol, Time[1]);
                }
            }
            #endregion

            #region Update Delta Velocity
            UpdateDeltaVelocity(barDelta);
            #endregion

            #region Calculate Volatility Regime & Z-Score
            VolatilityRegime volRegimeEnum = GetVolatilityRegime(totalBarVol);
            string volRegime = GetVolatilityRegimeString(volRegimeEnum);
            double volZScore = adaptiveReady ? GetZScore(totalBarVol, adaptiveVolumeBaseline, adaptiveVolumeStdDev) : 0;
            bool volRegimeGateAllowed = IsVolatilityRegimeAllowed(volRegimeEnum);
            #endregion

            #region Calculate Climax/Exhaustion
            bool isClimax, isExhaustion;
            double climaxScore, exhaustionScore;
            double priorBarVolumeForTelemetry = prevBarVolume;
            CalculateClimaxExhaustion(totalBarVol, currentBarRange, volZScore, 
                out isClimax, out isExhaustion, out climaxScore, out exhaustionScore);
            
            bool passClimaxFilter = EvaluateClimaxFilter(isClimax, isExhaustion);
            
            bool prevBarClimaxState = prevBarWasClimax;
            prevBarWasClimax = isClimax;
            #endregion

            #region Calculate Value Area Context
            ValueAreaContext vaContext = GetValueAreaContext(Close[1]);
            string vaContextStr = GetValueAreaContextString(vaContext);
            double priceDistToPOC = nyseValueAreaValid ? (Close[1] - nyseSessionPOC) / TickSize : 0;
            bool passVAFilter = EvaluateValueAreaFilter(vaContext, Close[1]);
            #endregion

            #region Calculate Delta Velocity Filter
            bool passDeltaVelocityFilter = EvaluateDeltaVelocityFilter();
            #endregion

            #region Imbalance Scanning
            int consecutiveBullish = 0, consecutiveBearish = 0;
            int maxBullishStack = 0, maxBearishStack = 0;
            double maxBullishStackTopTick = 0;
            double maxBearishStackTopTick = 0;
            double currentBullishImbVolSum = 0, currentBearishImbVolSum = 0;
            double tempMaxRatioBull = 0, tempMaxRatioBear = 0;
            double validBullishRatio = 0;
            double validAvgBullishImbVol = 0;
            double validBearishRatio = 0;
            double validAvgBearishImbVol = 0;
            int bullishImbalanceCount = 0, bearishImbalanceCount = 0;
            double bullishImbalanceDeltaSum = 0, bearishImbalanceDeltaSum = 0;

            int startTick = Convert.ToInt32(Math.Round(Low[1] / TickSize));
            int endTick = Convert.ToInt32(Math.Round(High[1] / TickSize));
            double maxVolAtPrice = 0;
            double pocTick = startTick;

            double avgVolPerTick = totalBarVol / Math.Max(1.0, (endTick - startTick + 1));

            double s3_lowZoneVol = 0, s3_lowBid = 0, s3_lowAsk = 0;
            double s3_highZoneVol = 0, s3_highBid = 0, s3_highAsk = 0;

            for (int t = startTick; t <= endTick; t++)
            {
                double p = Instrument.MasterInstrument.RoundToTickSize(t * TickSize);
                double askVol = confirmedBar.GetAskVolumeForPrice(p);
                double bidVol = confirmedBar.GetBidVolumeForPrice(p);
                double totalVolAtPrice = askVol + bidVol;

                if (totalVolAtPrice > maxVolAtPrice)
                {
                    maxVolAtPrice = totalVolAtPrice;
                    pocTick = t;
                }

                if (t <= startTick + S3_AbsorptionZoneTicks) { s3_lowZoneVol += totalVolAtPrice; s3_lowBid += bidVol; s3_lowAsk += askVol; }
                if (t >= endTick - S3_AbsorptionZoneTicks) { s3_highZoneVol += totalVolAtPrice; s3_highBid += bidVol; s3_highAsk += askVol; }

                double pMinusTick = Instrument.MasterInstrument.RoundToTickSize((t - 1) * TickSize);
                double pPlusTick = Instrument.MasterInstrument.RoundToTickSize((t + 1) * TickSize);

                double bidVolDiagonal = confirmedBar.GetBidVolumeForPrice(pMinusTick);
                double askVolDiagonal = confirmedBar.GetAskVolumeForPrice(pPlusTick);

                bool isBullish = false;
                double thisTickBullishRatio = 0;
                double thisTickBullishDelta = 0;
                bool bullHasComparison = true;
                double bullDen = 0;

                if (UseDiagonalImbalance)
                {
                    if (t > startTick) bullDen = bidVolDiagonal;
                    else
                    {
                        if (EdgeHandlingMode == ImbalanceEdgeHandlingMode.IgnoreEdgeLevels) bullHasComparison = false;
                        else if (EdgeHandlingMode == ImbalanceEdgeHandlingMode.HorizontalFallback) bullDen = bidVol;
                        else bullDen = 0;
                    }
                }
                else bullDen = bidVol;

                if (bullHasComparison && askVol >= MinImbalanceVolume)
                {
                    if (bullDen <= 0)
                    {
                        thisTickBullishRatio = double.MaxValue;
                        thisTickBullishDelta = askVol;
                        if (AllowInfiniteEdgeRatio) isBullish = true;
                    }
                    else
                    {
                        thisTickBullishRatio = askVol / bullDen;
                        thisTickBullishDelta = askVol - bullDen;
                        if (thisTickBullishRatio >= ImbalanceRatio && thisTickBullishRatio <= MaxImbalanceRatio)
                        {
                            isBullish = true;
                        }
                    }
                }

                if (isBullish)
                {
                    bullishImbalanceCount++;
                    if (thisTickBullishDelta > 0)
                        bullishImbalanceDeltaSum += thisTickBullishDelta;
                    consecutiveBullish++;
                    currentBullishImbVolSum += askVol;
                    if (thisTickBullishRatio > tempMaxRatioBull)
                        tempMaxRatioBull = thisTickBullishRatio;

                    if (consecutiveBullish > maxBullishStack)
                    {
                        maxBullishStack = consecutiveBullish;
                        maxBullishStackTopTick = t;
                        validBullishRatio = tempMaxRatioBull;
                        validAvgBullishImbVol = currentBullishImbVolSum / consecutiveBullish;
                    }
                    else if (consecutiveBullish == maxBullishStack && maxBullishStack > 0)
                    {
                        double currentAvgVol = currentBullishImbVolSum / consecutiveBullish;
                        if (tempMaxRatioBull > validBullishRatio || (tempMaxRatioBull == validBullishRatio && currentAvgVol > validAvgBullishImbVol))
                        {
                            maxBullishStackTopTick = t;
                            validBullishRatio = tempMaxRatioBull;
                            validAvgBullishImbVol = currentAvgVol;
                        }
                    }
                }
                else
                {
                    consecutiveBullish = 0;
                    currentBullishImbVolSum = 0;
                    tempMaxRatioBull = 0;
                }

                bool isBearish = false;
                double thisTickBearishRatio = 0;
                double thisTickBearishDelta = 0;
                bool bearHasComparison = true;
                double bearDen = 0;

                if (UseDiagonalImbalance)
                {
                    if (t < endTick) bearDen = askVolDiagonal;
                    else
                    {
                        if (EdgeHandlingMode == ImbalanceEdgeHandlingMode.IgnoreEdgeLevels) bearHasComparison = false;
                        else if (EdgeHandlingMode == ImbalanceEdgeHandlingMode.HorizontalFallback) bearDen = askVol;
                        else bearDen = 0;
                    }
                }
                else bearDen = askVol;

                if (bearHasComparison && bidVol >= MinImbalanceVolume)
                {
                    if (bearDen <= 0)
                    {
                        thisTickBearishRatio = double.MaxValue;
                        thisTickBearishDelta = bidVol;
                        if (AllowInfiniteEdgeRatio) isBearish = true;
                    }
                    else
                    {
                        thisTickBearishRatio = bidVol / bearDen;
                        thisTickBearishDelta = bidVol - bearDen;
                        if (thisTickBearishRatio >= ImbalanceRatio && thisTickBearishRatio <= MaxImbalanceRatio)
                        {
                            isBearish = true;
                        }
                    }
                }

                if (isBearish)
                {
                    bearishImbalanceCount++;
                    if (thisTickBearishDelta > 0)
                        bearishImbalanceDeltaSum += thisTickBearishDelta;
                    consecutiveBearish++;
                    currentBearishImbVolSum += bidVol;
                    if (thisTickBearishRatio > tempMaxRatioBear)
                        tempMaxRatioBear = thisTickBearishRatio;

                    if (consecutiveBearish > maxBearishStack)
                    {
                        maxBearishStack = consecutiveBearish;
                        maxBearishStackTopTick = t;
                        validBearishRatio = tempMaxRatioBear;
                        validAvgBearishImbVol = currentBearishImbVolSum / consecutiveBearish;
                    }
                    else if (consecutiveBearish == maxBearishStack && maxBearishStack > 0)
                    {
                        double currentAvgVolBear = currentBearishImbVolSum / consecutiveBearish;
                        if (tempMaxRatioBear > validBearishRatio || (tempMaxRatioBear == validBearishRatio && currentAvgVolBear > validAvgBearishImbVol))
                        {
                            maxBearishStackTopTick = t;
                            validBearishRatio = tempMaxRatioBear;
                            validAvgBearishImbVol = currentAvgVolBear;
                        }
                    }
                }
                else
                {
                    consecutiveBearish = 0;
                    currentBearishImbVolSum = 0;
                    tempMaxRatioBear = 0;
                }
            }
            #endregion

            #region Stack Cluster Analysis
            double bullStackTopPrice = maxBullishStackTopTick * TickSize;
            double bullStackBottomPrice = (maxBullishStackTopTick - maxBullishStack + 1) * TickSize;

            int bullClusterCount = 1;
            if (maxBullishStack > 0)
            {
                PruneRecentBullStacks();

                foreach (var s in recentBullStacks)
                {
                    double overlapBottom = bullStackBottomPrice > s.BottomPrice ? bullStackBottomPrice : s.BottomPrice;
                    double overlapTop = bullStackTopPrice < s.TopPrice ? bullStackTopPrice : s.TopPrice;
                    if (overlapTop >= overlapBottom) bullClusterCount++;
                }
                recentBullStacks.Add(new StackInfo { BarIndex = CurrentBar, BottomPrice = bullStackBottomPrice, TopPrice = bullStackTopPrice, Size = maxBullishStack });
                if (recentBullStacks.Count > maxStackMemory) recentBullStacks.RemoveAt(0);
            }

            double bearStackTopPrice = maxBearishStackTopTick * TickSize;
            double bearStackBottomPrice = (maxBearishStackTopTick - maxBearishStack + 1) * TickSize;

            int bearClusterCount = 1;
            if (maxBearishStack > 0)
            {
                PruneRecentBearStacks();

                foreach (var s in recentBearStacks)
                {
                    double overlapBottom = bearStackBottomPrice > s.BottomPrice ? bearStackBottomPrice : s.BottomPrice;
                    double overlapTop = bearStackTopPrice < s.TopPrice ? bearStackTopPrice : s.TopPrice;
                    if (overlapTop >= overlapBottom) bearClusterCount++;
                }
                recentBearStacks.Add(new StackInfo { BarIndex = CurrentBar, BottomPrice = bearStackBottomPrice, TopPrice = bearStackTopPrice, Size = maxBearishStack });
                if (recentBearStacks.Count > maxStackMemory) recentBearStacks.RemoveAt(0);
            }
            #endregion

            #region POC & Derived Metrics
            double currentPocPrice = pocTick * TickSize;

            double pocPosition = DefaultSessionPosition;
            if (endTick > startTick) pocPosition = (double)(pocTick - startTick) / (endTick - startTick);

            double pocVolPct = 0;
            if (totalBarVol > 0) pocVolPct = (maxVolAtPrice / totalBarVol) * 100.0;

            double domVolLongPercent = 0;
            if (totalBarVol > 0) domVolLongPercent = ((validAvgBullishImbVol * maxBullishStack) / totalBarVol) * 100.0;

            double escapeLongTicks = (Close[1] - (maxBullishStackTopTick * TickSize)) / TickSize;
            double stackMidTickLong = maxBullishStackTopTick - ((maxBullishStack - 1.0) / 2.0);

            double stackPosLong = DefaultSessionPosition;
            if (endTick > startTick) stackPosLong = (stackMidTickLong - startTick) / (double)(endTick - startTick);

            int cAdvLong = bullishImbalanceCount - bearishImbalanceCount;
            double dAdvLong = bullishImbalanceDeltaSum - bearishImbalanceDeltaSum;

            // Short-side derived metrics
            double domVolShortPercent = 0;
            if (totalBarVol > 0) domVolShortPercent = ((validAvgBearishImbVol * maxBearishStack) / totalBarVol) * 100.0;

            double maxBearishStackBottomTick = maxBearishStackTopTick - maxBearishStack + 1;
            double escapeShortTicks = (maxBearishStackBottomTick * TickSize - Close[1]) / TickSize;
            double stackMidTickShort = maxBearishStackTopTick - ((maxBearishStack - 1.0) / 2.0);

            double stackPosShort = DefaultSessionPosition;
            if (endTick > startTick) stackPosShort = (stackMidTickShort - startTick) / (double)(endTick - startTick);

            int cAdvShort = bearishImbalanceCount - bullishImbalanceCount;
            double dAdvShort = bearishImbalanceDeltaSum - bullishImbalanceDeltaSum;
            #endregion

            #region Market Regime Detection
            MarketRegime marketRegime = GetMarketRegime(vBarsType);
            string stateNameStr = GetMarketRegimeString(marketRegime);
            bool regimeAllowed = IsRegimeAllowed(marketRegime);
            #endregion

            #region Telemetry Calculations
            int barHighTick = Convert.ToInt32(Math.Round(High[1] / TickSize));
            int barLowTick = Convert.ToInt32(Math.Round(Low[1] / TickSize));

            double stackRecencyLong = CalculateStackRecency((int)maxBullishStackTopTick, maxBullishStack, barHighTick, barLowTick);
            double stackMidPriceLongCalc = (maxBullishStackTopTick - ((maxBullishStack - 1.0) / 2.0)) * TickSize;
            double sessionPosLong = GetSessionPosition(stackMidPriceLongCalc);
            SessionContext stackContextEnum = GetStackContext(sessionPosLong);
            string stackContextLong = GetSessionContextString(stackContextEnum);
            SessionLocationBucket sessionBucket = GetSessionLocationBucket(sessionPosLong);
            string sessionBucketStr = GetSessionLocationBucketString(sessionBucket);
            string spatialPairStr = GetSpatialPairLabel(sessionBucket, vaContext);

            // Short-side recency uses LOW of bar for recency calculation (bearish stack position from bottom)
            double stackRecencyShort = CalculateStackRecencyShort((int)maxBearishStackTopTick, maxBearishStack, barHighTick, barLowTick);
            double stackMidPriceShortCalc = (maxBearishStackTopTick - ((maxBearishStack - 1.0) / 2.0)) * TickSize;
            double sessionPosShort = GetSessionPosition(stackMidPriceShortCalc);
            SessionContext stackContextShortEnum = GetStackContext(sessionPosShort);
            string stackContextShort = GetSessionContextString(stackContextShortEnum);
            SessionLocationBucket sessionBucketShort = GetSessionLocationBucket(sessionPosShort);
            string sessionBucketShortStr = GetSessionLocationBucketString(sessionBucketShort);
            string spatialPairShortStr = GetSpatialPairLabel(sessionBucketShort, vaContext);

            double adaptiveMinVol = adaptiveReady ? adaptiveVolumeBaseline * AdaptiveVolumeMinMultiplier : S3_MinVolume;
            double adaptiveMaxVol = adaptiveReady ? adaptiveVolumeBaseline + (adaptiveVolumeStdDev * AdaptiveVolumeMaxStdDevMultiplier) : S3_MaxVolume;

            double timeBaseline = GetTimeAdjustedBaseline();
            double timeAdjustedMinVol = timeBaseline > 0 ? timeBaseline * TimeAdjustedVolumeMinMultiplier : adaptiveMinVol;

            double ftRate, ftAvgMfe, ftAvgMae;
            int ftSampleCount;
            GetFollowThroughStats(out ftRate, out ftAvgMfe, out ftAvgMae, out ftSampleCount);
            
            // Calculate Normalized Delta Metric
            double normDeltaPct = totalBarVol > 0 ? (barDelta / totalBarVol) * 100.0 : 0;
            #endregion

            #region POC Migration & Delta Divergence
            bool revUp = false;
            bool revDown = false;
            double pMig1 = 0;
            if (pocBarsProcessed >= 2 && totalBarVol > 0)
            {
                pMig1 = currentPocPrice - prevPoc1;
                double pMig2 = prevPoc1 - prevPoc2;
                revUp = (pMig1 > 0 && pMig2 <= 0);
                revDown = (pMig1 < 0 && pMig2 >= 0);
            }

            bool improvingDeltaLong = (barDelta > prevBarDelta1) && (prevBarDelta1 > prevBarDelta2);
            bool divLong = (barDelta > prevBarDelta1);
            bool improvingDeltaShort = (barDelta < prevBarDelta1) && (prevBarDelta1 < prevBarDelta2);
            bool divShort = (barDelta < prevBarDelta1);
            #endregion

            #region CD Slope Calculations
            int s3_lb = Math.Min(S3_CdLookback, CurrentBar - 1);

            double cdSlopeLog_S3_Long = CalculateCdSlopePct(vBarsType, s3_lb);

            double s3_olderSlope = CalculateCdSlopePct(vBarsType, s3_lb, S3_CdSlopeAccelShift);

            double s3_slopeAccel = cdSlopeLog_S3_Long - s3_olderSlope;
            #endregion

            #region Adaptive Context Matrix Prep
            int activeAnchorIdx = GetActiveAnchorIndex();
            bool activeAnchorReclaimed = GetActiveAnchorReclaimState();
            double activeLiveAvwap = 0;
            double activeHistoricalAvwap = 0;
            double activeAvwapDistTicks = 0;
            double activeAvwapSlopeDownTicks = 0;

            if (activeAnchorIdx > 0 && activeAnchorIdx <= CurrentBar - 1)
            {
                activeLiveAvwap = CalculateAVWAP(vBarsType, activeAnchorIdx, 1);
                activeHistoricalAvwap = GetAnchorHistoricalAVWAP(vBarsType, activeAnchorIdx);
                if (activeLiveAvwap > 0)
                {
                    activeAvwapDistTicks = (activeLiveAvwap - Close[1]) / TickSize;
                    activeAvwapSlopeDownTicks = activeHistoricalAvwap > 0 ? (activeHistoricalAvwap - activeLiveAvwap) / TickSize : 0;
                }
            }

            bool constantVolumeBarMode = IsConstantVolumeBarEnvironment(totalBarVol);
            AdaptiveContextFamily adaptiveContextFamily = GetAdaptiveContextFamily(sessionBucket, vaContext);
            AdaptiveRuleProfile adaptiveProfile = GetAdaptiveRuleProfile(adaptiveContextFamily, constantVolumeBarMode);
            AdaptiveContextFamily adaptiveContextFamilyShort = GetAdaptiveContextFamilyShort(sessionBucketShort, vaContext);
            AdaptiveRuleProfile adaptiveProfileShort = GetAdaptiveRuleProfileShort(adaptiveContextFamilyShort, constantVolumeBarMode);
            bool disableBarVolumeDependentFilters = constantVolumeBarMode && AutoDisableBarVolumeFiltersOnConstantVolume;
            if (UseAdaptiveContextMatrix && adaptiveProfile.DisableBarVolumeDependentFilters)
                disableBarVolumeDependentFilters = true;

            double signalBarRangeTicks = (High[1] - Low[1]) / TickSize;
            double signalBarSecs = (CurrentBar >= 2) ? (Time[1] - Time[2]).TotalSeconds : 0;
            bool rangeBarMode = IsRangeBarEnvironment();
            double signalClosePosPct = GetSignalClosePositionPct();
            double signalBodyPct = GetSignalBodyPct();
            double signalUpperWickPct = GetSignalUpperWickPct();
            double signalLowerWickPct = GetSignalLowerWickPct();
            double signalOverlapPct = GetSignalOverlapPct();
            string rangePaceLabel = rangeBarMode ? GetRangePaceLabel(signalBarSecs) : "N/A";
            double rangePer1kVolumeTicks = totalBarVol > 0 ? signalBarRangeTicks * (1000.0 / totalBarVol) : 0;
            double deltaPerTick = signalBarRangeTicks > 0 ? barDelta / signalBarRangeTicks : 0;
            double deltaPctOfVolume = totalBarVol > 0 ? (barDelta / totalBarVol) * 100.0 : 0;
            double imbalanceDensity = signalBarRangeTicks > 0 ? bullishImbalanceCount / signalBarRangeTicks : bullishImbalanceCount;
            double signalSessionMid = sessionInitialized ? (sessionLow + sessionHigh) / 2.0 : 0;
            double priceToSessionLowTicks = sessionInitialized ? GetSignedTicksToReference(Close[1], sessionLow) : 0;
            double priceToSessionHighTicks = sessionInitialized ? GetSignedTicksToReference(Close[1], sessionHigh) : 0;
            double priceToSessionMidTicks = signalSessionMid > 0 ? GetSignedTicksToReference(Close[1], signalSessionMid) : 0;
            double priceToVALTicks = nyseValueAreaValid ? GetSignedTicksToReference(Close[1], nyseSessionVAL) : 0;
            double priceToVAHTicks = nyseValueAreaValid ? GetSignedTicksToReference(Close[1], nyseSessionVAH) : 0;
            double priceToPOCSignedTicks = nyseValueAreaValid ? GetSignedTicksToReference(Close[1], nyseSessionPOC) : 0;
            double lowZonePct = totalBarVol > 0 ? (s3_lowZoneVol / totalBarVol) * 100.0 : 0;
            double highZonePct = totalBarVol > 0 ? (s3_highZoneVol / totalBarVol) * 100.0 : 0;

            double distToVWAPTicksSigned = activeLiveAvwap > 0 ? GetSignedTicksToReference(Close[1], activeLiveAvwap) : double.MaxValue;
            double distToPDHTicksSigned = priorDayHigh > 0 ? GetSignedTicksToReference(Close[1], priorDayHigh) : double.MaxValue;
            double distToPDLTicksSigned = priorDayLow > 0 ? GetSignedTicksToReference(Close[1], priorDayLow) : double.MaxValue;
            double distToIBHTicksSigned = (initialBalanceHigh > 0 && initialBalanceHigh != double.MinValue) ? GetSignedTicksToReference(Close[1], initialBalanceHigh) : double.MaxValue;
            double distToIBLTicksSigned = (initialBalanceLow > 0 && initialBalanceLow != double.MaxValue) ? GetSignedTicksToReference(Close[1], initialBalanceLow) : double.MaxValue;
            double distToPMHTicksSigned = premarketInitialized ? GetSignedTicksToReference(Close[1], premarketHigh) : double.MaxValue;
            double distToPMLTicksSigned = premarketInitialized ? GetSignedTicksToReference(Close[1], premarketLow) : double.MaxValue;

            bool nearVWAP = distToVWAPTicksSigned != double.MaxValue && Math.Abs(distToVWAPTicksSigned) <= KeyLevelProximityTicks;
            bool nearPDH = distToPDHTicksSigned != double.MaxValue && Math.Abs(distToPDHTicksSigned) <= KeyLevelProximityTicks;
            bool nearPDL = distToPDLTicksSigned != double.MaxValue && Math.Abs(distToPDLTicksSigned) <= KeyLevelProximityTicks;
            bool nearIBH = distToIBHTicksSigned != double.MaxValue && Math.Abs(distToIBHTicksSigned) <= KeyLevelProximityTicks;
            bool nearIBL = distToIBLTicksSigned != double.MaxValue && Math.Abs(distToIBLTicksSigned) <= KeyLevelProximityTicks;
            bool nearPMH = distToPMHTicksSigned != double.MaxValue && Math.Abs(distToPMHTicksSigned) <= KeyLevelProximityTicks;
            bool nearPML = distToPMLTicksSigned != double.MaxValue && Math.Abs(distToPMLTicksSigned) <= KeyLevelProximityTicks;
            bool nearPOC = nyseValueAreaValid && Math.Abs(priceToPOCSignedTicks) <= KeyLevelProximityTicks;

            string nearestKeyLevel = "NONE";
            double nearestKeyLevelAbsTicks = double.MaxValue;
            ConsiderNearestKeyLevel("VWAP", distToVWAPTicksSigned, ref nearestKeyLevel, ref nearestKeyLevelAbsTicks);
            ConsiderNearestKeyLevel("PDH", distToPDHTicksSigned, ref nearestKeyLevel, ref nearestKeyLevelAbsTicks);
            ConsiderNearestKeyLevel("PDL", distToPDLTicksSigned, ref nearestKeyLevel, ref nearestKeyLevelAbsTicks);
            ConsiderNearestKeyLevel("IBH", distToIBHTicksSigned, ref nearestKeyLevel, ref nearestKeyLevelAbsTicks);
            ConsiderNearestKeyLevel("IBL", distToIBLTicksSigned, ref nearestKeyLevel, ref nearestKeyLevelAbsTicks);
            ConsiderNearestKeyLevel("PMH", distToPMHTicksSigned, ref nearestKeyLevel, ref nearestKeyLevelAbsTicks);
            ConsiderNearestKeyLevel("PML", distToPMLTicksSigned, ref nearestKeyLevel, ref nearestKeyLevelAbsTicks);
            ConsiderNearestKeyLevel("POC", nyseValueAreaValid ? priceToPOCSignedTicks : double.MaxValue, ref nearestKeyLevel, ref nearestKeyLevelAbsTicks);

            string keyLevelSummary = BuildKeyLevelSummary(
                nearVWAP, distToVWAPTicksSigned,
                nearPDH, distToPDHTicksSigned,
                nearPDL, distToPDLTicksSigned,
                nearIBH, distToIBHTicksSigned,
                nearIBL, distToIBLTicksSigned,
                nearPMH, distToPMHTicksSigned,
                nearPML, distToPMLTicksSigned,
                nearPOC, priceToPOCSignedTicks);

            bool absorptionStrongForLevel = lowZonePct >= 30.0;
            bool keyLevelGatePass = EvaluateKeyLevelGate(
                nearVWAP, nearPDH, nearPDL, nearIBH, nearIBL, nearPMH, nearPML, nearPOC,
                deltaPctOfVolume, absorptionStrongForLevel, Time[1], sessionBucket);

            string adaptiveRuleSummary = "";
            string matrixProofState = "MATRIX-OFF";
            string matrixBlockReason = "";
            #endregion

            #region Per-Bar Regime Telemetry
            // Time[1] and Close[1] reference the just-confirmed bar; all regime metrics are calculated from confirmed bar data

            // Update microstructure regime rolling window on every RTH bar (independent of adaptiveReady)
            if (IsWithinNYSESession(Time[1]))
                UpdateMicrostructureRegime(rangePer1kVolumeTicks);

            if (UseTradeLogging && adaptiveReady && IsWithinNYSESession(Time[1]))
            {
                double barRegimeSessPos = GetSessionPosition(Close[1]);
                string barRegimeContext = GetSessionContextString(GetStackContext(barRegimeSessPos));
                Print(string.Format("[BAR-REGIME] Time={0:yyyy-MM-dd HH:mm:ss} | R1k={1:F1} | VolZ={2:F2} | BarVol={3:F0} | Range={4:F1}T | Secs={5:F2} | Delta={6:F0} | NormDelta={7:F1}% | SessPos={8:F2} | Context={9} | Momentum={10} | RollR1k={11:F1} | Regime={12}",
                    Time[1], rangePer1kVolumeTicks, volZScore, totalBarVol, signalBarRangeTicks, signalBarSecs,
                    barDelta, normDeltaPct, barRegimeSessPos, barRegimeContext, GetDeltaMomentumString(currentDeltaMomentum),
                    rollingR1k, GetMicroRegimeString(currentMicroRegime)));
            }
            #endregion

            #region Tier A Long Validation
            bool s3_long_valid = false;
            bool longEntryTaken = false;

            if (S3_Enable && maxBullishStack >= S3_MinStackSize && maxBullishStack <= S3_MaxStackSize)
            {
                s3_long_valid = true;

                // Bull Count Filter
                if (S3_UseBullCount && (bullishImbalanceCount < S3_MinBullCount || bullishImbalanceCount > S3_MaxBullCount)) s3_long_valid = false;

                if (S3_UseCdSlope && (cdSlopeLog_S3_Long < S3_MinCdSlope || cdSlopeLog_S3_Long > S3_MaxCdSlope)) s3_long_valid = false;
                if (S3_RequireDivergence && marketRegime != MarketRegime.BullDiv) s3_long_valid = false;
                if (!disableBarVolumeDependentFilters && S3_UseMinVolume && totalBarVol < S3_MinVolume) s3_long_valid = false;
                if (!disableBarVolumeDependentFilters && S3_UseMaxVolume && totalBarVol > S3_MaxVolume) s3_long_valid = false;
                if (S3_UseMaxImbVol && validAvgBullishImbVol > S3_MaxImbVol) s3_long_valid = false;
                if (S3_UseDominance && (cAdvLong < S3_MinDomCount || dAdvLong < S3_MinDomDelta)) s3_long_valid = false;
                
                // Volume Spike Filter
                if (!disableBarVolumeDependentFilters && S3_UseVolumeSpike)
                {
                    if (currentVolSpikeRatio < S3_MinVolumeSpikeRatio || currentVolSpikeRatio > S3_MaxVolumeSpikeRatio) s3_long_valid = false;
                }

                // POC Checks
                if (S3_UseMinPoc && pocPosition < S3_MinPoc) s3_long_valid = false;
                if (S3_UsePoc && pocPosition > S3_MaxPoc) s3_long_valid = false;
                
                // Recency Check
                if (S3_UseRecency && (stackRecencyLong < S3_MinRecency || stackRecencyLong > S3_MaxRecency)) s3_long_valid = false;

                bool effectiveUseMinEscape = UseAdaptiveContextMatrix ? adaptiveProfile.UseMinEscape : S3_UseMinEscape;
                double effectiveMinEscape = UseAdaptiveContextMatrix ? adaptiveProfile.MinEscape : S3_MinEscape;
                bool effectiveUseMaxEscape = UseAdaptiveContextMatrix ? adaptiveProfile.UseMaxEscape : S3_UseMaxEscape;
                double effectiveMaxEscape = UseAdaptiveContextMatrix ? adaptiveProfile.MaxEscape : S3_MaxEscape;

                if (effectiveUseMinEscape && escapeLongTicks < effectiveMinEscape) s3_long_valid = false;
                if (effectiveUseMaxEscape && escapeLongTicks > effectiveMaxEscape) s3_long_valid = false;

                adaptiveRuleSummary = string.Format(
                    "Pair={0} | Family={1} | ConstVol={2} | DisableBarVol={3} | EscMin={4} | EscMax={5} | DomMin={6} | DomMax={7} | RatioMin={8:F1} | ReqImpDelta={9} | ReqPosDelta={10} | ReqPocLift={11} | ReqAvwapReclaim={12} | CeilingTrap={13} ({14:F1}%)",
                    spatialPairStr,
                    GetAdaptiveContextFamilyString(adaptiveContextFamily),
                    constantVolumeBarMode,
                    disableBarVolumeDependentFilters,
                    effectiveUseMinEscape ? effectiveMinEscape.ToString("F1") : "OFF",
                    effectiveUseMaxEscape ? effectiveMaxEscape.ToString("F1") : "OFF",
                    adaptiveProfile.UseMinDomVol ? adaptiveProfile.MinDomVol.ToString("F1") : "OFF",
                    adaptiveProfile.UseMaxDomVol ? adaptiveProfile.MaxDomVol.ToString("F1") : "OFF",
                    adaptiveProfile.MinRatio,
                    adaptiveProfile.RequireImprovingDelta,
                    adaptiveProfile.RequirePositiveBarDelta,
                    adaptiveProfile.RequirePocLift,
                    adaptiveProfile.RequireAvwapReclaim,
                    adaptiveProfile.UseCeilingTrapKillSwitch,
                    adaptiveProfile.CeilingTrapAbsorptionPct);

                if (!UseAdaptiveContextMatrix)
                {
                    if (S3_UseMinDomVol && domVolLongPercent < S3_MinDomVol) s3_long_valid = false;
                    if (S3_UseMaxDomVol && domVolLongPercent > S3_MaxDomVol) s3_long_valid = false;
                }
                
                // Bar Quality & Delta Filter
                if (S3_UseBarDelta && (barDelta < S3_MinBarDelta || barDelta > S3_MaxBarDelta)) s3_long_valid = false;
                if (S3_UseNormalizedDelta && (normDeltaPct < S3_MinNormalizedDeltaPct || normDeltaPct > S3_MaxNormalizedDeltaPct)) s3_long_valid = false;

                if (S3_UseMinOppStack && maxBearishStack < S3_MinOppStack) s3_long_valid = false;
                if (S3_UseMaxOppStack && maxBearishStack > S3_MaxOppStack) s3_long_valid = false;

                if (S3_UseDeltaDivergence)
                {
                    if (S3_RequireDeceleration && !improvingDeltaLong) s3_long_valid = false;
                    else if (!S3_RequireDeceleration && !divLong) s3_long_valid = false;
                }

                if (S3_UseCdSlopeAccel && s3_slopeAccel < S3_MinCdSlopeAccel) s3_long_valid = false;

                double s3_absPct = (totalBarVol > 0) ? (s3_lowZoneVol / totalBarVol) * 100.0 : 0;
                double s3_absMult = s3_lowBid / Math.Max(1.0, avgVolPerTick);
                
                // Max Absorption Ceiling
                if (S3_UseAbsorption)
                {
                    if (s3_absPct < S3_MinAbsorptionPct) s3_long_valid = false;
                    if (S3_UseMaxAbsorption && s3_absPct > S3_MaxAbsorptionPct) s3_long_valid = false;
                    if (s3_absMult < S3_MinAbsorptionMultiple) s3_long_valid = false;
                }

                if (S3_UsePocMigration)
                {
                    if (pocBarsProcessed < 2) s3_long_valid = false;
                    else
                    {
                        if (S3_RequirePocReversal && !revUp) s3_long_valid = false;
                        if (pMig1 / TickSize < S3_MinPocMigrationTicks) s3_long_valid = false;
                    }
                }

                // AVWAP 4-TIER ENGINE
                if (UseAvwapFilter)
                {
                    if (activeAnchorIdx <= 0 || activeAnchorIdx > CurrentBar - 1)
                    {
                        s3_long_valid = false;
                    }
                    else
                    {
                        // 1. Calculate precise decision-time distance below VWAP (Positive = Below, Negative = Above)
                        double distTicks = activeAvwapDistTicks;
                        bool allowAdaptiveCeilingAvwapOverride = UseAdaptiveContextMatrix && adaptiveContextFamily == AdaptiveContextFamily.CeilingBreakout;

                        // 2. VWAP Acceptance Rule: Must have touched or traded above the ACTIVE anchor VWAP at least once
                        if (UseVwapAcceptanceFilter && !activeAnchorReclaimed)
                            s3_long_valid = false;

                        // 3. SLOPE VETO: Don't fight a downward trend (Noise-adjusted)
                        if (UseAvwapSlopeFilter && activeHistoricalAvwap > 0 && activeLiveAvwap > 0)
                        {
                            if (activeAvwapSlopeDownTicks >= AvwapSlopeVetoTicks && !allowAdaptiveCeilingAvwapOverride)
                                s3_long_valid = false;
                        }

                        // 4. TIER 1: THE DEADZONE & ABOVE VWAP (Too close to VWAP or Above it)
                        if (distTicks < AvwapDeadzoneTicks)
                        {
                            if (!allowAdaptiveCeilingAvwapOverride)
                                s3_long_valid = false; // Blocks chop and trades above VWAP
                        }
                        // 5. TIER 4: THE KILLZONE (Extreme falling knife, too far to save)
                        else if (distTicks > AvwapKillzoneTicks)
                        {
                            s3_long_valid = false; // Hard block in the killzone
                        }
                        // 6. TIER 3: THE EXTREME ZONE (Falling Knife Protection)
                        else if (distTicks > AvwapExtremeTicks)
                        {
                            // Require explicit proof of a stall to catch the knife
                            bool hasAbsorptionStallProof = S3_UseAbsorption
                                && s3_absPct >= S3_MinAbsorptionPct
                                && (!S3_UseMaxAbsorption || s3_absPct <= S3_MaxAbsorptionPct)
                                && s3_absMult >= S3_MinAbsorptionMultiple;

                            bool hasStallProof = isExhaustion || isClimax || improvingDeltaLong || hasAbsorptionStallProof;

                            if (!hasStallProof)
                                s3_long_valid = false;
                        }
                        // 7. TIER 2: THE SWEET SPOT (Normal rules apply, between Deadzone and Extreme)
                        else 
                        {
                            // Pass (Do nothing, let standard footprint rules apply)
                        }
                    }
                }

                if (UseKeyLevelGate && !keyLevelGatePass)
                    s3_long_valid = false;

                // ── GLOBAL GATES (applied after per-filter checks, before matrix) ──────────
                // VOLATILITY REGIME GATE
                if (UseVolatilityRegimeGate && !volRegimeGateAllowed)
                    s3_long_valid = false;

                // MICROSTRUCTURE REGIME GATE
                if (!IsMicroRegimeAllowed())
                {
                    if (UseTradeLogging)
                        Print(string.Format("[REGIME-BLOCK] Regime={0} | RollR1k={1:F1} | Signal skipped",
                            GetMicroRegimeString(currentMicroRegime), rollingR1k));
                    s3_long_valid = false;
                }

                // SESSION CONTEXT FILTER
                if (UseSessionContextFilter && !IsSessionContextAllowed(stackContextEnum))
                    s3_long_valid = false;

                // ADAPTIVE 40 RANGE FILTER (C3)
                bool adaptive40RangePass = EvaluateAdaptive40RangeFilter(stackContextEnum, currentDeltaMomentum, cAdvLong);
                if (!adaptive40RangePass)
                    s3_long_valid = false;

                // ES 8-RANGE FILTER (C3-3)
                bool esRangeFilterPass = EvaluateESRangeFilter(stackContextEnum, currentDeltaMomentum, adaptiveContextFamily, volRegimeEnum, activeAvwapDistTicks);
                if (!esRangeFilterPass)
                    s3_long_valid = false;

                // PHASE 1 RULE #1: Block SESS-LOW-REV (Any Vol Regime)
                if (BlockSessLowRev && stackContextEnum == SessionContext.SessionLowRev)
                {
                    if (UseTradeLogging)
                        Print("BLOCK: SESS-LOW-REV context blocked by Phase1 Rule #1");
                    s3_long_valid = false;
                }

                // PHASE 1 RULE #2: Block SESS-HIGH-BO + ACTIVE + ABOVE-VAH
                if (BlockCeilingActiveAboveVAH && stackContextEnum == SessionContext.SessionHighBo && volRegimeEnum == VolatilityRegime.Active && vaContext == ValueAreaContext.AboveVAH)
                {
                    if (UseTradeLogging)
                        Print("BLOCK: SESS-HIGH-BO + ACTIVE + ABOVE-VAH blocked by Phase1 Rule #2");
                    s3_long_valid = false;
                }

                // W2 RULE B: Block LOWER-CONT + BELOW-VAL + (NORMAL or QUIET)
                if (BlockLowerContBelowValLowVol && stackContextEnum == SessionContext.LowerCont && vaContext == ValueAreaContext.BelowVAL
                    && (volRegimeEnum == VolatilityRegime.Normal || volRegimeEnum == VolatilityRegime.Quiet))
                {
                    if (UseTradeLogging)
                        Print("BLOCK: LOWER-CONT + BELOW-VAL + NORMAL/QUIET blocked by W2 Rule B");
                    s3_long_valid = false;
                }

                // W2 RULE C: Block SESS-HIGH-BO + AT-VAH (any VolRegime)
                if (BlockCeilingAtVAH && stackContextEnum == SessionContext.SessionHighBo && vaContext == ValueAreaContext.AtVAH)
                {
                    if (UseTradeLogging)
                        Print("BLOCK: SESS-HIGH-BO + AT-VAH blocked by W2 Rule C");
                    s3_long_valid = false;
                }

                // W2 RULE F: Block LOWER-CONT + Cluster>=2
                if (BlockLowerContCluster2 && stackContextEnum == SessionContext.LowerCont && bullClusterCount >= 2)
                {
                    if (UseTradeLogging)
                        Print("BLOCK: LOWER-CONT + Cluster>=2 blocked by W2 Rule F");
                    s3_long_valid = false;
                }

                // SIGNAL QUALITY: Min Bar Duration
                bool passMinBarSecs = !UseMinBarSecs || signalBarSecs >= MinBarSecsThreshold;
                if (!passMinBarSecs)
                    s3_long_valid = false;

                // SIGNAL QUALITY: Max Escape Global
                bool passMaxEscapeGlobal = !UseMaxEscapeGlobal || escapeLongTicks <= MaxEscapeGlobalTicks;
                if (!passMaxEscapeGlobal)
                    s3_long_valid = false;

                // ─────────────────────────────────────────────────────────────────────────────

                // 1. Capture the exact state of the global filters BEFORE the matrix touches it
                bool preMatrixPass = s3_long_valid;
                bool matrixVerdict = true; // Innocent until proven guilty by the Matrix

                if (UseAdaptiveContextMatrix)
                {
                    switch (adaptiveContextFamily)
                    {
                        case AdaptiveContextFamily.BasementValueReclaim:
                        {
                            bool clusterOrDomPass = bullClusterCount >= 2 || domVolLongPercent >= adaptiveProfile.MinDomVol;
                            if (!clusterOrDomPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "BasementValue: needs bull cluster >= 2 or DomVol support";
                            }

                            bool valueHoldGate = improvingDeltaLong || divLong || ((s3_absMult >= 1.5) && (escapeLongTicks <= 0));
                            if (!valueHoldGate)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "BasementValue: needs improving delta/divergence or absorption hold";
                            }

                            bool reclaimPass = !adaptiveProfile.RequireAvwapReclaim || activeAnchorIdx <= 0 || activeAnchorReclaimed;
                            if (!reclaimPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "BasementValue: active AVWAP reclaim required";
                            }

                            matrixProofState = string.Format("ClusterOrDom={0} | ValueHold={1} (ImpDelta OR Div OR AbsMult>=1.5 & Esc<=0) | Reclaim={2}",
                                clusterOrDomPass, valueHoldGate, reclaimPass);
                            break;
                        }

                        case AdaptiveContextFamily.BelowValueReversal:
                        {
                            bool isLargeConstVol = constantVolumeBarMode && totalBarVol >= 1400;
                            double effectiveDomMin = isLargeConstVol ? Math.Min(adaptiveProfile.MinDomVol, 1.0) : adaptiveProfile.MinDomVol;
                            double effectiveRatioMin = isLargeConstVol ? Math.Min(adaptiveProfile.MinRatio, 4.0) : adaptiveProfile.MinRatio;

                            bool clusterOrDomPass = bullClusterCount >= 2 || domVolLongPercent >= effectiveDomMin;
                            if (!clusterOrDomPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "BelowVAL: needs bull cluster >= 2 or DomVol support";
                            }

                            bool reversalGateA = improvingDeltaLong && (barDelta > 0) && (validBullishRatio >= effectiveRatioMin);
                            bool reversalGateB = (s3_absMult >= 2.0) && (escapeLongTicks <= 0);
                            bool reversalProof = reversalGateA || reversalGateB;
                            if (!reversalProof)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "BelowVAL: needs positive reclaim proof or absorption reversal";
                            }

                            bool reclaimPass = !adaptiveProfile.RequireAvwapReclaim || activeAnchorIdx <= 0 || activeAnchorReclaimed;
                            bool strong1500ReclaimWaiver = isLargeConstVol && reclaimPass && reversalGateA && pocPosition >= 0.55;
                            bool strongImpulseReversalWaiver =
                                reclaimPass
                                && (
                                    (reversalGateA
                                        && escapeLongTicks <= 0
                                        && validBullishRatio >= Math.Max(effectiveRatioMin + 1.0, 8.0)
                                        && domVolLongPercent >= Math.Max(effectiveDomMin, 45.0))
                                    || (reversalGateB
                                        && domVolLongPercent >= Math.Max(effectiveDomMin, 35.0))
                                   );

                            bool pocLiftPass = !adaptiveProfile.RequirePocLift
                                || ((pocBarsProcessed >= 2) && (pMig1 > 0 || revUp))
                                || strong1500ReclaimWaiver
                                || strongImpulseReversalWaiver;
                            if (!pocLiftPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "BelowVAL: POC lift required";
                            }

                            if (!reclaimPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "BelowVAL: active AVWAP reclaim required";
                            }

                            bool chasePass = !adaptiveProfile.UseMaxEscape || (escapeLongTicks <= adaptiveProfile.MaxEscape);
                            if (!chasePass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "BelowVAL: too extended for reversal entry";
                            }

                            matrixProofState = string.Format("ClusterOrDom={0} | GateA(ImpDelta & BarDelta>0 & Ratio>={1:F1})={2} | GateB(AbsMult>=2 & Esc<=0)={3} | POCUp={4} | Reclaim={5} | ChasePass={6} (Esc<={7:F1}) | 1500Waiver={8} | StrongImpulseWaiver={9}",
                                clusterOrDomPass, effectiveRatioMin, reversalGateA, reversalGateB, pocLiftPass, reclaimPass, chasePass, adaptiveProfile.MaxEscape, strong1500ReclaimWaiver, strongImpulseReversalWaiver);
                            break;
                        }

                        case AdaptiveContextFamily.WithGrainContinuation:
                        {
                            bool domPass = domVolLongPercent >= adaptiveProfile.MinDomVol;
                            if (!domPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "Continuation: DomVol below minimum";
                            }

                            bool slopePass = !(activeAnchorIdx > 0 && activeHistoricalAvwap > 0 && activeAvwapSlopeDownTicks >= AvwapSlopeVetoTicks);
                            if (!slopePass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "Continuation: AVWAP slope veto";
                            }

                            matrixProofState = string.Format("DomPass={0} (Need>={1:F1}) | SlopePass={2} | ActiveSlopeDrop={3:F1}T",
                                domPass, adaptiveProfile.MinDomVol, slopePass, activeAvwapSlopeDownTicks);
                            break;
                        }

                        case AdaptiveContextFamily.CeilingBreakout:
                        {
                            bool isLargeConstVol = constantVolumeBarMode && totalBarVol >= 1400;
                            bool ceilingIntensityPass = (domVolLongPercent >= adaptiveProfile.MinDomVol) || (validBullishRatio >= adaptiveProfile.MinRatio);
                            if (!ceilingIntensityPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "Ceiling: needs DomVol or Ratio breakout intensity";
                            }

                            bool ceilingTrapPass = !(adaptiveProfile.UseCeilingTrapKillSwitch && s3_absPct >= adaptiveProfile.CeilingTrapAbsorptionPct && barDelta < 0);
                            if (!ceilingTrapPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "Ceiling: trap kill switch fired";
                            }

                            bool ceilingSlopePass = !(activeAnchorIdx > 0 && activeHistoricalAvwap > 0 && activeAvwapSlopeDownTicks >= AvwapSlopeVetoTicks && !ceilingIntensityPass);
                            if (!ceilingSlopePass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "Ceiling: AVWAP slope veto without intensity override";
                            }

                            bool ceilingAntiChasePass;
                            if (isLargeConstVol)
                            {
                                bool positiveChase = deltaPctOfVolume > 5.0 || (deltaPctOfVolume > 0 && signalBarSecs < 70.0);
                                bool domOverheat = domVolLongPercent > 12.0;
                                ceilingAntiChasePass = !(positiveChase || domOverheat);
                            }
                            else
                            {
                                ceilingAntiChasePass = !(deltaPctOfVolume > 0 || domVolLongPercent > 10.0);
                            }

                            if (!ceilingAntiChasePass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "Ceiling: anti-chase filter tripped";
                            }

                            bool ceilingWeakFailurePass = !(isLargeConstVol && deltaPctOfVolume <= -8.0 && pocPosition < 0.30 && validBullishRatio < 5.0);
                            if (!ceilingWeakFailurePass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "Ceiling: weak negative-delta breakout structure";
                            }

                            matrixProofState = string.Format("IntensityPass={0} (Dom>={1:F1} OR Ratio>={2:F1}) | TrapPass={3} | SlopePass={4} | AntiChasePass={5} (D/V={6:F1}% | DomVol={7:F1}% | Secs={8:F1}) | WeakFailPass={9} | ActiveSlopeDrop={10:F1}T",
                                ceilingIntensityPass, adaptiveProfile.MinDomVol, adaptiveProfile.MinRatio, ceilingTrapPass, ceilingSlopePass, ceilingAntiChasePass, deltaPctOfVolume, domVolLongPercent, signalBarSecs, ceilingWeakFailurePass, activeAvwapSlopeDownTicks);
                            break;
                        }

                        case AdaptiveContextFamily.MidRangeChop:
                        {
                            bool isLargeConstVol = constantVolumeBarMode && totalBarVol >= 1400;
                            double effectiveDomMin = isLargeConstVol ? Math.Min(adaptiveProfile.MinDomVol, 4.0) : adaptiveProfile.MinDomVol;
                            double effectiveRatioMin = isLargeConstVol ? Math.Min(adaptiveProfile.MinRatio, 2.0) : adaptiveProfile.MinRatio;

                            bool strongSingleBarMidWaiver =
                                (barDelta > 0)
                                && (validBullishRatio >= (isLargeConstVol ? 4.0 : Math.Max(effectiveRatioMin + 1.0, 8.0)))
                                && (domVolLongPercent >= (isLargeConstVol ? 4.0 : Math.Max(effectiveDomMin, 45.0)))
                                && (deltaPctOfVolume >= (isLargeConstVol ? 10.0 : 40.0))
                                && (signalBarSecs > 0)
                                && (signalBarSecs <= (isLargeConstVol ? 70.0 : 8.0));

                            bool clusterPass = bullClusterCount >= 2 || strongSingleBarMidWaiver;
                            if (!clusterPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "MidRange: needs bull cluster >= 2";
                            }

                            bool domPass = domVolLongPercent >= effectiveDomMin;
                            if (!domPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "MidRange: DomVol below minimum";
                            }

                            bool ratioPass = validBullishRatio >= effectiveRatioMin;
                            if (!ratioPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "MidRange: ratio below minimum";
                            }

                            bool improvingPass = !adaptiveProfile.RequireImprovingDelta || improvingDeltaLong || strongSingleBarMidWaiver;
                            if (!improvingPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "MidRange: improving delta required";
                            }

                            bool positiveDeltaPass = !adaptiveProfile.RequirePositiveBarDelta || barDelta > 0;
                            if (!positiveDeltaPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "MidRange: positive bar delta required";
                            }

                            bool slowRotation1500Pass = isLargeConstVol
                                && signalBarSecs >= 55.0
                                && escapeLongTicks <= 0
                                && deltaPctOfVolume <= -8.0
                                && activeAnchorReclaimed
                                && (validBullishRatio >= 2.0 || domVolLongPercent >= 4.0);

                            if (slowRotation1500Pass)
                            {
                                matrixVerdict = true;
                                matrixBlockReason = "PASS";
                            }

                            matrixProofState = string.Format("ClusterPass={0} | DomPass={1} (Need>={2:F1}) | RatioPass={3} (Need>={4:F1}) | ImprovingDelta={5} | PositiveBarDelta={6} | SlowRotation1500={7} (Secs={8:F1} | Escape={9:F1} | D/V={10:F1}%) | StrongImpulseWaiver={11}",
                                clusterPass, domPass, effectiveDomMin, ratioPass, effectiveRatioMin, improvingPass, positiveDeltaPass, slowRotation1500Pass, signalBarSecs, escapeLongTicks, deltaPctOfVolume, strongSingleBarMidWaiver);
                            break;
                        }

                        case AdaptiveContextFamily.UpperValueFriction:
                        {
                            bool isLargeConstVol = constantVolumeBarMode && totalBarVol >= 1400;
                            double effectiveDomMin = isLargeConstVol ? Math.Min(adaptiveProfile.MinDomVol, 2.0) : adaptiveProfile.MinDomVol;
                            double effectiveRatioMin = isLargeConstVol ? Math.Min(adaptiveProfile.MinRatio, 4.0) : adaptiveProfile.MinRatio;

                            bool domPass = domVolLongPercent >= effectiveDomMin;
                            if (!domPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "UpperFriction: DomVol below minimum";
                            }

                            bool ratioPass = validBullishRatio >= effectiveRatioMin;
                            if (!ratioPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "UpperFriction: ratio below minimum";
                            }

                            bool reclaimPass = !adaptiveProfile.RequireAvwapReclaim || activeAnchorIdx <= 0 || activeAnchorReclaimed;
                            if (!reclaimPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "UpperFriction: active AVWAP reclaim required";
                            }

                            bool trapPass = !(adaptiveProfile.UseCeilingTrapKillSwitch && s3_absPct >= adaptiveProfile.CeilingTrapAbsorptionPct && barDelta < 0);
                            if (!trapPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "UpperFriction: trap kill switch fired";
                            }

                            bool improvingRoutePass = improvingDeltaLong && ratioPass;
                            bool slowPullbackRoutePass = signalBarSecs >= (isLargeConstVol ? 70.0 : 50.0) && escapeLongTicks <= 0 && deltaPctOfVolume > (isLargeConstVol ? -12.0 : -10.0);
                            bool calibrated1500RoutePass = isLargeConstVol && reclaimPass && signalBarSecs >= 70.0 && escapeLongTicks <= 0 && deltaPctOfVolume <= -7.0 && (domVolLongPercent >= 2.0 || validBullishRatio >= 3.0);

                            bool structurePass = improvingRoutePass || slowPullbackRoutePass || calibrated1500RoutePass;
                            if (!structurePass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "UpperFriction: needs improving-delta ratio proof or slow-pullback reclaim";
                            }

                            if (calibrated1500RoutePass)
                            {
                                matrixVerdict = true;
                                matrixBlockReason = "PASS";
                            }

                            matrixProofState = string.Format("DomPass={0} (Need>={1:F1}) | RatioPass={2} (Need>={3:F1}) | Reclaim={4} | TrapPass={5} | ImprovingRoute={6} | SlowPullbackRoute={7} (Secs={8:F1} | Escape={9:F1} | D/V={10:F1}%) | Cal1500Route={11}",
                                domPass, effectiveDomMin, ratioPass, effectiveRatioMin, reclaimPass, trapPass, improvingRoutePass, slowPullbackRoutePass, signalBarSecs, escapeLongTicks, deltaPctOfVolume, calibrated1500RoutePass);
                            break;
                        }

                        case AdaptiveContextFamily.LocationConflict:
                        {
                            bool isLargeConstVol = constantVolumeBarMode && totalBarVol >= 1400;
                            double effectiveDomMin = isLargeConstVol ? Math.Min(adaptiveProfile.MinDomVol, 1.0) : adaptiveProfile.MinDomVol;
                            double effectiveRatioMin = isLargeConstVol ? Math.Min(adaptiveProfile.MinRatio, 6.0) : adaptiveProfile.MinRatio;

                            bool domPass = domVolLongPercent >= effectiveDomMin;
                            if (!domPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "LocationConflict: DomVol below minimum";
                            }

                            bool ratioPass = validBullishRatio >= effectiveRatioMin;
                            if (!ratioPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "LocationConflict: ratio below minimum";
                            }

                            bool improvingPass = !adaptiveProfile.RequireImprovingDelta || improvingDeltaLong;
                            if (!improvingPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "LocationConflict: improving delta required";
                            }

                            bool positiveDeltaPass = !adaptiveProfile.RequirePositiveBarDelta || barDelta > 0;
                            if (!positiveDeltaPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "LocationConflict: positive bar delta required";
                            }

                            bool pocLiftPass = !adaptiveProfile.RequirePocLift || ((pocBarsProcessed >= 2) && (pMig1 > 0 || revUp));
                            if (!pocLiftPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "LocationConflict: POC lift required";
                            }

                            bool reclaimPass = !adaptiveProfile.RequireAvwapReclaim || activeAnchorIdx <= 0 || activeAnchorReclaimed;
                            if (!reclaimPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "LocationConflict: active AVWAP reclaim required";
                            }

                            bool trapPass = !(adaptiveProfile.UseCeilingTrapKillSwitch && s3_absPct >= adaptiveProfile.CeilingTrapAbsorptionPct && barDelta < 0);
                            if (!trapPass)
                            {
                                matrixVerdict = false;
                                if (string.IsNullOrEmpty(matrixBlockReason))
                                    matrixBlockReason = "LocationConflict: trap kill switch fired";
                            }

                            bool conflict1500RotationPass = isLargeConstVol && reclaimPass && signalBarSecs >= 40.0 && escapeLongTicks <= 0 && deltaPctOfVolume <= 0 && (domPass || ratioPass);
                            if (conflict1500RotationPass)
                            {
                                matrixVerdict = true;
                                matrixBlockReason = "PASS";
                            }

                            matrixProofState = string.Format("DomPass={0} (Need>={1:F1}) | RatioPass={2} (Need>={3:F1}) | ImprovingDelta={4} | PositiveBarDelta={5} | POCUp={6} | Reclaim={7} | TrapPass={8} | Conflict1500Rotate={9}",
                                domPass, effectiveDomMin, ratioPass, effectiveRatioMin, improvingPass, positiveDeltaPass, pocLiftPass, reclaimPass, trapPass, conflict1500RotationPass);
                            break;
                        }
                    }
                }

                bool rangeBarVerdict = true;
                string rangeBarBlockReason = "";
                string rangeBarProofState = "";

                bool runRangeBarAdaptation = UseRangeBarAdaptation && rangeBarMode
                    && ((UseAdaptiveContextMatrix && matrixVerdict) || !UseAdaptiveContextMatrix);

                if (runRangeBarAdaptation)
                {
                    bool rangeBarPass = true;
                    string rangeBarReason = "";
                    string rangeBarState = "";

                    switch (adaptiveContextFamily)
                    {
                        case AdaptiveContextFamily.WithGrainContinuation:
                        case AdaptiveContextFamily.UpperValueFriction:
                        case AdaptiveContextFamily.CeilingBreakout:
                        {
                            double contCloseMin = adaptiveContextFamily == AdaptiveContextFamily.CeilingBreakout
                                ? Math.Max(RangeContinuationCloseMinPct, 0.75)
                                : RangeContinuationCloseMinPct;

                            bool closePass = signalClosePosPct >= contCloseMin;
                            bool overlapPass = signalOverlapPct <= RangeMaxOverlapPct;
                            bool wickPass = signalUpperWickPct <= Math.Max(0.15, 1.0 - contCloseMin);
                            bool slowBarPass = signalBarSecs < RangeSlowBarSecsThreshold || signalClosePosPct >= RangeStrongSlowBarCloseMinPct;

                            rangeBarPass = closePass && overlapPass && wickPass && slowBarPass;
                            if (!rangeBarPass)
                                rangeBarReason = string.Format("RangeBar: continuation quality failed (ClosePos={0:P0} | UpperWick={1:P0} | Overlap={2:P0} | Secs={3:F1})", signalClosePosPct, signalUpperWickPct, signalOverlapPct, signalBarSecs);

                            rangeBarState = string.Format("ClosePass={0} (Need>={1:P0}) | UpperWickPass={2} (Max<={3:P0}) | OverlapPass={4} (Max<={5:P0}) | SlowBarPass={6} (NeedClose>={7:P0} when Secs>={8:F0})",
                                closePass, contCloseMin, wickPass, Math.Max(0.15, 1.0 - contCloseMin), overlapPass, RangeMaxOverlapPct, slowBarPass, RangeStrongSlowBarCloseMinPct, RangeSlowBarSecsThreshold);
                            break;
                        }

                        case AdaptiveContextFamily.LocationConflict:
                        {
                            bool conflictReclaimShapePass = signalClosePosPct >= 0.60 || signalLowerWickPct >= RangeMinRejectionWickPct;
                            bool conflictOverlapPass = signalOverlapPct <= Math.Min(0.90, RangeMaxOverlapPct + 0.15);
                            rangeBarPass = conflictReclaimShapePass && conflictOverlapPass;
                            if (!rangeBarPass)
                                rangeBarReason = string.Format("RangeBar: conflict shape failed (ClosePos={0:P0} | LowerWick={1:P0} | Overlap={2:P0})", signalClosePosPct, signalLowerWickPct, signalOverlapPct);

                            rangeBarState = string.Format("ConflictShapePass={0} (ClosePos={1:P0} | LowerWick={2:P0}) | ConflictOverlapPass={3} (Overlap={4:P0})",
                                conflictReclaimShapePass, signalClosePosPct, signalLowerWickPct, conflictOverlapPass, signalOverlapPct);
                            break;
                        }
                    }

                    if (!string.IsNullOrEmpty(rangeBarState))
                        rangeBarProofState = rangeBarState;

                    if (!rangeBarPass)
                    {
                        rangeBarVerdict = false;
                        rangeBarBlockReason = rangeBarReason;
                    }
                }

                if (!string.IsNullOrEmpty(rangeBarProofState))
                {
                    if (string.IsNullOrEmpty(matrixProofState))
                        matrixProofState = "RangeBar=" + rangeBarProofState;
                    else
                        matrixProofState += " | RangeBar=" + rangeBarProofState;
                }

                if (!rangeBarVerdict && string.IsNullOrEmpty(matrixBlockReason))
                    matrixBlockReason = rangeBarBlockReason;

                if (UseAdaptiveContextMatrix && string.IsNullOrEmpty(matrixProofState))
                    matrixProofState = "No family-specific matrix rules fired";

                if (UseAdaptiveContextMatrix && matrixVerdict && string.IsNullOrEmpty(matrixBlockReason))
                    matrixBlockReason = "PASS";
            #endregion

            #region Signal Validation
            bool baseStackValid = (S3_Enable && maxBullishStack >= S3_MinStackSize && maxBullishStack <= S3_MaxStackSize);
            bool fullEnginePass = preMatrixPass && matrixVerdict;
            bool preAdaptPass = preMatrixPass && rangeBarVerdict;
            bool fullAdaptivePass = fullEnginePass && rangeBarVerdict;

            if (UseAdaptiveContextMatrix)
            {
                if (ShadowMatrixMode)
                {
                    // Shadow mode: do not block trades. Log the matrix verdict, but execute off the pre-matrix pass,
                    // while still allowing the standalone range-bar adaptation branch to operate.
                    s3_long_valid = preAdaptPass;
                }
                else
                {
                    // Matrix authority mode: adaptive context matrix controls execution, then range-bar adaptation can further refine it.
                    s3_long_valid = fullAdaptivePass;
                }
            }
            else
            {
                // Legacy Tier A / pre-matrix behavior when adaptive matrix is disabled, but standalone range-bar adaptation may still refine it.
                s3_long_valid = preAdaptPass;
            }

            bool cooldownOkEval = CooldownWindowComplete(Time[0]);
            bool validLongSignal = s3_long_valid && cooldownOkEval;
            #endregion

            #region Entry Execution
            if (Position.MarketPosition == MarketPosition.Flat)
            {
                if (AllowLongTrades && validLongSignal)
                {
                    // Capture Entry Snapshot - Existing Fields
                    lastEntryContext = stackContextLong;
                    lastEntryVolRegime = volRegime;
                    lastEntryStackRecency = stackRecencyLong;
                    lastEntrySessionPos = sessionPosLong;
                    lastEntryVolZScore = volZScore;
                    lastEntryAdaptiveMinVol = adaptiveMinVol;
                    lastEntryAdaptiveMaxVol = adaptiveMaxVol;
                    lastEntryTimeBaseline = timeBaseline;
                    lastEntryFollowThroughRate = ftRate;
                    lastEntryAvgMfe = ftAvgMfe;
                    lastEntryClusterCount = bullClusterCount;

                    lastEntryAdaptiveVolBase = adaptiveVolumeBaseline;
                    lastEntryAdaptiveVolStdDev = adaptiveVolumeStdDev;
                    lastEntryTotalBarVol = totalBarVol;
                    lastEntryVolumeSpikeRatio = currentVolSpikeRatio;
                    lastEntryTimeAdjMinVol = timeAdjustedMinVol;
                    lastEntryFtSampleCount = ftSampleCount;
                    lastEntryFtAvgMae = ftAvgMae;
                    lastEntryNetCnt = cAdvLong;
                    lastEntryRegimeAllowed = regimeAllowed;
                    lastEntryBaseStackPass = baseStackValid;
                    lastEntryPreMatrixPass = preMatrixPass;
                    lastEntryMatrixVerdict = matrixVerdict;

                    lastEntryBarDelta = barDelta;
                    lastEntryNormDeltaPct = normDeltaPct;
                    lastEntryBarDir = barDir;
                    lastEntryPrevBarDelta1 = prevBarDelta1;
                    lastEntryPrevBarDelta2 = prevBarDelta2;
                    lastEntryImprovingDelta = improvingDeltaLong;
                    lastEntryDivLong = divLong;
                    lastEntryPocMig1 = pMig1 / TickSize;
                    lastEntryRevUp = revUp;
                    lastEntryCurrentPoc = currentPocPrice;
                    lastEntryPrevPoc1 = prevPoc1;
                    lastEntryPrevPoc2 = prevPoc2;

                    lastEntryVolRegimeGateAllowed = volRegimeGateAllowed;

                    // Microstructure regime telemetry
                    lastEntryRollingR1k = rollingR1k;
                    lastEntryMicroRegime = GetMicroRegimeString(currentMicroRegime);

                    // Session context & signal quality gate telemetry
                    lastEntrySessionContextGateAllowed = IsSessionContextAllowed(stackContextEnum);
                    lastEntryMinSecsPass = passMinBarSecs;
                    lastEntryMaxEscapeGlobalPass = passMaxEscapeGlobal;
                    lastEntryAdaptive40RangeFilterPass = adaptive40RangePass;
                    lastEntryESRangeFilterPass = esRangeFilterPass;

                    lastEntryBarIsClimax = isClimax;
                    lastEntryBarIsExhaustion = isExhaustion;
                    lastEntryPrevBarWasClimax = prevBarClimaxState;
                    lastEntryClimaxScore = climaxScore;
                    lastEntryExhaustionScore = exhaustionScore;
                    lastEntryClimaxPrevVol = priorBarVolumeForTelemetry;
                    lastEntryClimaxCurVol = totalBarVol;
                    lastEntryPassClimaxFilter = passClimaxFilter;
                    lastEntryPassExhaustionFilter = !UseExhaustionFilter || isExhaustion || !RequireExhaustionSetup;

                    lastEntryVAH = nyseSessionVAH;
                    lastEntryVAL = nyseSessionVAL;
                    lastEntrySessionPOCVA = nyseSessionPOC;
                    lastEntryVAContext = vaContextStr;
                    lastEntryPriceDistToPOC = priceDistToPOC;
                    lastEntryPassVAFilter = passVAFilter;

                    lastEntryDeltaROC = currentDeltaROC;
                    lastEntryDeltaAccel = currentDeltaAccel;
                    lastEntryDeltaVelocityScore = deltaVelocityScore;
                    lastEntryDeltaMomentum = GetDeltaMomentumString(currentDeltaMomentum);
                    lastEntryPassDeltaVelocityFilter = passDeltaVelocityFilter;

                    // Tier A Snapshot Data
                    lastEntryOlderSlope = s3_olderSlope;
                    lastEntrySlopeAccel = s3_slopeAccel;
                    lastEntryPassCdAccel = !S3_UseCdSlopeAccel || (s3_slopeAccel >= S3_MinCdSlopeAccel);

                    lastEntryPassDeltaDiv = !S3_UseDeltaDivergence || (S3_RequireDeceleration ? lastEntryImprovingDelta : lastEntryDivLong);

                    lastEntryLowZoneVol = s3_lowZoneVol;
                    lastEntryLowBid = s3_lowBid;
                    lastEntryLowAsk = s3_lowAsk;
                    lastEntryAbsPct = (totalBarVol > 0) ? (s3_lowZoneVol / totalBarVol) * 100.0 : 0;
                    lastEntryAbsMult = s3_lowBid / Math.Max(1.0, avgVolPerTick);
                    
                    lastEntryPassAbsorb = !S3_UseAbsorption || 
                                          ((lastEntryAbsPct >= S3_MinAbsorptionPct) && 
                                           (!S3_UseMaxAbsorption || lastEntryAbsPct <= S3_MaxAbsorptionPct) && 
                                           (lastEntryAbsMult >= S3_MinAbsorptionMultiple));

                    lastEntryPassPocMig = !S3_UsePocMigration || ((pocBarsProcessed >= 2) && (!S3_RequirePocReversal || lastEntryRevUp) && (lastEntryPocMig1 >= S3_MinPocMigrationTicks));

                    lastEntryAdaptiveFamily = GetAdaptiveContextFamilyString(adaptiveContextFamily);
                    lastEntryAdaptiveRuleSummary = adaptiveRuleSummary;
                    lastEntryMatrixProofState = matrixProofState;
                    lastEntryMatrixBlockReason = matrixBlockReason;
                    lastEntryConstantVolumeMode = constantVolumeBarMode;
                    lastEntryDisableBarVolumeFilters = disableBarVolumeDependentFilters;
                    lastEntrySessionAxis = sessionBucketStr;
                    lastEntrySpatialPair = spatialPairStr;

                    lastEntrySignalPrice = Close[1];
                    lastEntrySessionHigh = sessionHigh;
                    lastEntrySessionLow = sessionLow;
                    lastEntrySessionMid = signalSessionMid;
                    lastEntrySignalBarRangeTicks = signalBarRangeTicks;
                    lastEntrySignalBarSecs = signalBarSecs;
                    lastEntryRangePer1kVolumeTicks = rangePer1kVolumeTicks;
                    lastEntryDeltaPerTick = deltaPerTick;
                    lastEntryDeltaPctOfVolume = deltaPctOfVolume;
                    lastEntryImbalanceDensity = imbalanceDensity;
                    lastEntryPocVolPct = pocVolPct;
                    lastEntryMaxVolAtPrice = maxVolAtPrice;
                    lastEntryUpperZoneVol = s3_highZoneVol;
                    lastEntryUpperZonePct = highZonePct;
                    lastEntryLowZonePct = lowZonePct;
                    lastEntryBullishImbalanceCount = bullishImbalanceCount;
                    lastEntryBearishImbalanceCount = bearishImbalanceCount;
                    lastEntryMaxBullishStack = maxBullishStack;
                    lastEntryMaxBearishStack = maxBearishStack;
                    lastEntryEscapeTicks = escapeLongTicks;
                    lastEntryDomVolPercent = domVolLongPercent;
                    lastEntryValidBullishRatio = validBullishRatio == double.MaxValue ? 999.0 : validBullishRatio;
                    lastEntryPocPosition = pocPosition;
                    lastEntryRangeBarMode = rangeBarMode;
                    lastEntryRangePace = rangePaceLabel;
                    lastEntryRangeClosePos = signalClosePosPct;
                    lastEntryRangeBodyPct = signalBodyPct;
                    lastEntryRangeOverlapPct = signalOverlapPct;
                    lastEntryRangeLowerWickPct = signalLowerWickPct;
                    lastEntryRangeUpperWickPct = signalUpperWickPct;
                    lastEntryPriceToSessionLowTicks = priceToSessionLowTicks;
                    lastEntryPriceToSessionHighTicks = priceToSessionHighTicks;
                    lastEntryPriceToSessionMidTicks = priceToSessionMidTicks;
                    lastEntryPriceToVALTicks = priceToVALTicks;
                    lastEntryPriceToVAHTicks = priceToVAHTicks;
                    lastEntryPriceToPOCSignedTicks = priceToPOCSignedTicks;
                    lastEntryKeyLevelSummary = keyLevelSummary;
                    lastEntryNearestKeyLevel = nearestKeyLevel;
                    lastEntryNearestKeyLevelDistTicks = nearestKeyLevelAbsTicks == double.MaxValue ? 0 : nearestKeyLevelAbsTicks;
                    lastEntryNearVWAP = nearVWAP;
                    lastEntryNearPDH = nearPDH;
                    lastEntryNearPDL = nearPDL;
                    lastEntryNearIBH = nearIBH;
                    lastEntryNearIBL = nearIBL;
                    lastEntryNearPMH = nearPMH;
                    lastEntryNearPML = nearPML;
                    lastEntryNearPOC = nearPOC;
                    lastEntryKeyLevelGatePass = keyLevelGatePass;

                    // Build Trade Log
                    string localTradeLog = "";
                    if (UseTradeLogging)
                    {
                        string tierName = "TIER A";
                        double loggedCdSlope = cdSlopeLog_S3_Long;
                        double logRatioLong = validBullishRatio == double.MaxValue ? 999.0 : validBullishRatio;

                        var logSb = new StringBuilder();
                        logSb.AppendFormat("SigBar: {0} | Entry: {{ENTRY_TIME}} | LONG ({1}) | SigPx: {2} | Dir: {3} | ",
                            Time[1].ToString("yyyy-MM-dd HH:mm:ss"), tierName, Close[1], barDir);
                        logSb.AppendFormat("BarDelta: {0:F0} | Stack: {1} (Pos: {2:F2} | Ratio: {3:F1} | OppStack: {4}) | ",
                            barDelta, maxBullishStack, stackPosLong, logRatioLong, maxBearishStack);
                        logSb.AppendFormat("ImbVol: {0:F1} | Vol: {1} | POC: {2:F2} (PocVol: {3:F0} / {4:F1}%) | ",
                            validAvgBullishImbVol, totalBarVol, pocPosition, maxVolAtPrice, pocVolPct);
                        logSb.AppendFormat("CvdState: {0} (Allowed: {1}) | ImbCount: [{2}B/{3}S/NetCnt: {4}/NetD: {5:+0;-0;0}] | Escape: {6:F0}T | ",
                            stateNameStr, regimeAllowed, bullishImbalanceCount, bearishImbalanceCount, cAdvLong, dAdvLong, escapeLongTicks);
                        logSb.AppendFormat("DomVol: {0:F1}% | CD Slope: {1:F2}% | CtxFam: {2} | Pair: {3} | KeyLvl: {4} | SigRange: {5:F1}T | SigSecs: {6:F2} | R1k: {7:F1}T | D/V: {8:F1}%",
                            domVolLongPercent, loggedCdSlope, GetAdaptiveContextFamilyString(adaptiveContextFamily), spatialPairStr, nearestKeyLevel, signalBarRangeTicks, signalBarSecs, rangePer1kVolumeTicks, deltaPctOfVolume);

                        localTradeLog = logSb.ToString();
                    }

                    pendingTradeLog = localTradeLog.Replace("{ENTRY_TIME}", Time[0].ToString("yyyy-MM-dd HH:mm:ss"));
                    
                    // Capture AVWAP snapshots for Telemetry logging
                    CaptureAnchorAvwapTelemetry(
                        vBarsType, rthOpenBarIdx, hasReclaimedOpenVwap,
                        out lastEntryAvwapOpen, out lastEntryAvwapOpenHistorical, out lastEntryAvwapOpenSignalDistTicks,
                        out lastEntryAvwapOpenSlopeDropTicks, out lastEntryAvwapOpenTier, out lastEntryAvwapOpenSlope, out lastEntryAvwapOpenReclaimed);

                    CaptureAnchorAvwapTelemetry(
                        vBarsType, sessionHighBarIdx, hasReclaimedHighVwap,
                        out lastEntryAvwapHigh, out lastEntryAvwapHighHistorical, out lastEntryAvwapHighSignalDistTicks,
                        out lastEntryAvwapHighSlopeDropTicks, out lastEntryAvwapHighTier, out lastEntryAvwapHighSlope, out lastEntryAvwapHighReclaimed);

                    CaptureAnchorAvwapTelemetry(
                        vBarsType, sessionLowBarIdx, hasReclaimedLowVwap,
                        out lastEntryAvwapLow, out lastEntryAvwapLowHistorical, out lastEntryAvwapLowSignalDistTicks,
                        out lastEntryAvwapLowSlopeDropTicks, out lastEntryAvwapLowTier, out lastEntryAvwapLowSlope, out lastEntryAvwapLowReclaimed);

                    lastEntryAvwapActiveAnchor = "N/A";
                    lastEntryAvwapTier = "N/A";
                    lastEntryAvwapSlope = "N/A";
                    lastEntryAvwapSlopeDropTicks = 0;
                    lastEntryAvwapSignalDistTicks = 0;
                    lastEntryAvwapReclaimed = false;

                    switch (AvwapAnchor)
                    {
                        case AvwapAnchorType.SessionOpen:
                            lastEntryAvwapActiveAnchor = "OPEN";
                            lastEntryAvwapTier = lastEntryAvwapOpenTier;
                            lastEntryAvwapSlope = lastEntryAvwapOpenSlope;
                            lastEntryAvwapSlopeDropTicks = lastEntryAvwapOpenSlopeDropTicks;
                            lastEntryAvwapSignalDistTicks = lastEntryAvwapOpenSignalDistTicks;
                            lastEntryAvwapReclaimed = lastEntryAvwapOpenReclaimed;
                            break;
                        case AvwapAnchorType.SessionHigh:
                            lastEntryAvwapActiveAnchor = "HIGH";
                            lastEntryAvwapTier = lastEntryAvwapHighTier;
                            lastEntryAvwapSlope = lastEntryAvwapHighSlope;
                            lastEntryAvwapSlopeDropTicks = lastEntryAvwapHighSlopeDropTicks;
                            lastEntryAvwapSignalDistTicks = lastEntryAvwapHighSignalDistTicks;
                            lastEntryAvwapReclaimed = lastEntryAvwapHighReclaimed;
                            break;
                        case AvwapAnchorType.SessionLow:
                            lastEntryAvwapActiveAnchor = "LOW";
                            lastEntryAvwapTier = lastEntryAvwapLowTier;
                            lastEntryAvwapSlope = lastEntryAvwapLowSlope;
                            lastEntryAvwapSlopeDropTicks = lastEntryAvwapLowSlopeDropTicks;
                            lastEntryAvwapSignalDistTicks = lastEntryAvwapLowSignalDistTicks;
                            lastEntryAvwapReclaimed = lastEntryAvwapLowReclaimed;
                            break;
                    }

                    if (UseTradeLogging)
                        Print(string.Format("Immediate Entry | EntryBar={0:yyyy-MM-dd HH:mm:ss} | B1={1:HH:mm:ss} O1={2} C1={3}",
                            Time[0], Time[1], Open[1], Close[1]));

                    // Spread telemetry — use bar-level accumulated data when available, fall back to instantaneous
                    double currentBid = GetCurrentBid();
                    double currentAsk = GetCurrentAsk();
                    double currentSpread = (currentAsk > 0 && currentBid > 0) ? (currentAsk - currentBid) / TickSize : 0;
                    lastEntrySignalSpread = currentSpread;
                    lastEntryAvgSpread = barSpreadCount > 0 ? barSpreadSum / barSpreadCount : currentSpread;
                    lastEntryMaxSpread = barSpreadCount > 0 ? barSpreadMax : currentSpread;
                    lastEntryBookBidVol = 0;  // Placeholder pending OnMarketDepth() integration
                    lastEntryBookAskVol = 0;  // Placeholder pending OnMarketDepth() integration

                    EnterLong("MomLE");
                    longEntryTaken = true;
                }
            }
            #endregion
            } // closes S3 long if

            #region Tier A Short Validation and Entry
            bool passMinBarSecsShort = true;
            bool passMaxEscapeGlobalShort = true;

            if (AllowShortTrades && !longEntryTaken && Position.MarketPosition == MarketPosition.Flat
                && S3_Enable && maxBearishStack >= S3_MinStackSize && maxBearishStack <= S3_MaxStackSize)
            {
                bool s3_short_valid = true;

                // Bear Count Filter (mirrors S3_UseBullCount)
                if (S3_UseBullCount && (bearishImbalanceCount < S3_MinBullCount || bearishImbalanceCount > S3_MaxBullCount)) s3_short_valid = false;

                // CD Slope: for shorts require NEGATIVE slope (selling pressure)
                if (S3_UseCdSlope && (cdSlopeLog_S3_Long > -S3_MinCdSlope || cdSlopeLog_S3_Long < -S3_MaxCdSlope)) s3_short_valid = false;
                if (S3_RequireDivergence && marketRegime != MarketRegime.BearDiv) s3_short_valid = false;
                if (!disableBarVolumeDependentFilters && S3_UseMinVolume && totalBarVol < S3_MinVolume) s3_short_valid = false;
                if (!disableBarVolumeDependentFilters && S3_UseMaxVolume && totalBarVol > S3_MaxVolume) s3_short_valid = false;
                if (S3_UseMaxImbVol && validAvgBearishImbVol > S3_MaxImbVol) s3_short_valid = false;
                if (S3_UseDominance && (cAdvShort < S3_MinDomCount || dAdvShort < S3_MinDomDelta)) s3_short_valid = false;

                // Volume Spike Filter
                if (!disableBarVolumeDependentFilters && S3_UseVolumeSpike)
                {
                    if (currentVolSpikeRatio < S3_MinVolumeSpikeRatio || currentVolSpikeRatio > S3_MaxVolumeSpikeRatio) s3_short_valid = false;
                }

                // POC Checks: for shorts, HIGH POC position is favorable
                if (S3_UseMinPoc && pocPosition > (1.0 - S3_MinPoc)) s3_short_valid = false;
                if (S3_UsePoc && pocPosition < (1.0 - S3_MaxPoc)) s3_short_valid = false;

                // Recency Check
                if (S3_UseRecency && (stackRecencyShort < S3_MinRecency || stackRecencyShort > S3_MaxRecency)) s3_short_valid = false;

                bool effectiveUseMinEscapeShort = UseAdaptiveContextMatrix ? adaptiveProfileShort.UseMinEscape : S3_UseMinEscape;
                double effectiveMinEscapeShort = UseAdaptiveContextMatrix ? adaptiveProfileShort.MinEscape : S3_MinEscape;
                bool effectiveUseMaxEscapeShort = UseAdaptiveContextMatrix ? adaptiveProfileShort.UseMaxEscape : S3_UseMaxEscape;
                double effectiveMaxEscapeShort = UseAdaptiveContextMatrix ? adaptiveProfileShort.MaxEscape : S3_MaxEscape;

                if (effectiveUseMinEscapeShort && escapeShortTicks < effectiveMinEscapeShort) s3_short_valid = false;
                if (effectiveUseMaxEscapeShort && escapeShortTicks > effectiveMaxEscapeShort) s3_short_valid = false;

                if (!UseAdaptiveContextMatrix)
                {
                    if (S3_UseMinDomVol && domVolShortPercent < S3_MinDomVol) s3_short_valid = false;
                    if (S3_UseMaxDomVol && domVolShortPercent > S3_MaxDomVol) s3_short_valid = false;
                }

                // Bar Quality & Delta Filter (for shorts: negative delta favored)
                if (S3_UseBarDelta && (barDelta > -S3_MinBarDelta || barDelta < -S3_MaxBarDelta)) s3_short_valid = false;
                if (S3_UseNormalizedDelta && (normDeltaPct > -S3_MinNormalizedDeltaPct || normDeltaPct < -S3_MaxNormalizedDeltaPct)) s3_short_valid = false;

                if (S3_UseMinOppStack && maxBullishStack < S3_MinOppStack) s3_short_valid = false;
                if (S3_UseMaxOppStack && maxBullishStack > S3_MaxOppStack) s3_short_valid = false;

                if (S3_UseDeltaDivergence)
                {
                    if (S3_RequireDeceleration && !improvingDeltaShort) s3_short_valid = false;
                    else if (!S3_RequireDeceleration && !divShort) s3_short_valid = false;
                }

                if (S3_UseCdSlopeAccel && s3_slopeAccel > -S3_MinCdSlopeAccel) s3_short_valid = false;

                // Absorption: Check HIGH zone for shorts (supply absorption at the top)
                double s3_absShortPct = (totalBarVol > 0) ? (s3_highZoneVol / totalBarVol) * 100.0 : 0;
                double s3_absShortMult = s3_highAsk / Math.Max(1.0, avgVolPerTick);

                if (S3_UseAbsorption)
                {
                    if (s3_absShortPct < S3_MinAbsorptionPct) s3_short_valid = false;
                    if (S3_UseMaxAbsorption && s3_absShortPct > S3_MaxAbsorptionPct) s3_short_valid = false;
                    if (s3_absShortMult < S3_MinAbsorptionMultiple) s3_short_valid = false;
                }

                if (S3_UsePocMigration)
                {
                    if (pocBarsProcessed < 2) s3_short_valid = false;
                    else
                    {
                        if (S3_RequirePocReversal && !revDown) s3_short_valid = false;
                        if (-pMig1 / TickSize < S3_MinPocMigrationTicks) s3_short_valid = false;
                    }
                }

                // AVWAP 4-TIER ENGINE (for shorts)
                if (UseAvwapFilter)
                {
                    if (activeAnchorIdx <= 0 || activeAnchorIdx > CurrentBar - 1)
                    {
                        s3_short_valid = false;
                    }
                    else
                    {
                        // For shorts: distance is ABOVE VWAP (positive = above = favorable)
                        double distTicksShort = (Close[1] - activeLiveAvwap) / TickSize;

                        // VWAP Acceptance Rule
                        if (UseVwapAcceptanceFilter && !activeAnchorReclaimed)
                            s3_short_valid = false;

                        // SLOPE VETO: For shorts, rising VWAP = veto (don't fight uptrend)
                        if (UseAvwapSlopeFilter && activeHistoricalAvwap > 0 && activeLiveAvwap > 0)
                        {
                            double slopeUpTicks = (activeLiveAvwap - activeHistoricalAvwap) / TickSize;
                            if (slopeUpTicks >= AvwapSlopeVetoTicks)
                                s3_short_valid = false;
                        }

                        // TIER 1: DEADZONE & BELOW VWAP (too close or below VWAP)
                        if (distTicksShort < AvwapDeadzoneTicks)
                        {
                            s3_short_valid = false;
                        }
                        // TIER 4: KILLZONE (too far above VWAP)
                        else if (distTicksShort > AvwapKillzoneTicks)
                        {
                            s3_short_valid = false;
                        }
                        // TIER 3: EXTREME ZONE (stall proof required)
                        else if (distTicksShort > AvwapExtremeTicks)
                        {
                            bool hasAbsorptionStallProofShort = S3_UseAbsorption
                                && s3_absShortPct >= S3_MinAbsorptionPct
                                && (!S3_UseMaxAbsorption || s3_absShortPct <= S3_MaxAbsorptionPct)
                                && s3_absShortMult >= S3_MinAbsorptionMultiple;

                            bool hasStallProofShort = isExhaustion || isClimax || improvingDeltaShort || hasAbsorptionStallProofShort;

                            if (!hasStallProofShort)
                                s3_short_valid = false;
                        }
                        // TIER 2: SWEET SPOT
                        // else: pass
                    }
                }

                if (UseKeyLevelGate && !keyLevelGatePass)
                    s3_short_valid = false;

                // GLOBAL GATES
                if (UseVolatilityRegimeGate && !volRegimeGateAllowed)
                    s3_short_valid = false;

                if (!IsMicroRegimeAllowed())
                    s3_short_valid = false;

                if (UseSessionContextFilter && !IsSessionContextAllowed(stackContextShortEnum))
                    s3_short_valid = false;

                passMinBarSecsShort = !UseMinBarSecs || signalBarSecs >= MinBarSecsThreshold;
                if (!passMinBarSecsShort)
                    s3_short_valid = false;

                passMaxEscapeGlobalShort = !UseMaxEscapeGlobal || escapeShortTicks <= MaxEscapeGlobalTicks;
                if (!passMaxEscapeGlobalShort)
                    s3_short_valid = false;

                // Adaptive Context Matrix for shorts
                bool preMatrixPassShort = s3_short_valid;
                bool matrixVerdictShort = true;
                string matrixProofStateShort = "";
                string matrixBlockReasonShort = "";

                if (UseAdaptiveContextMatrix)
                {
                    switch (adaptiveContextFamilyShort)
                    {
                        case AdaptiveContextFamily.CeilingValueReject:
                        {
                            bool clusterOrDomPassShort = bearClusterCount >= 2 || domVolShortPercent >= adaptiveProfileShort.MinDomVol;
                            if (!clusterOrDomPassShort)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "CeilingReject: needs bear cluster >= 2 or DomVol support";
                            }

                            bool valueRejectGate = improvingDeltaShort || divShort || ((s3_absShortMult >= 1.5) && (escapeShortTicks <= 0));
                            if (!valueRejectGate)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "CeilingReject: needs improving delta/divergence or absorption supply";
                            }

                            bool reclaimPassShort = !adaptiveProfileShort.RequireAvwapReclaim || activeAnchorIdx <= 0 || activeAnchorReclaimed;
                            if (!reclaimPassShort)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "CeilingReject: active AVWAP reclaim required";
                            }

                            matrixProofStateShort = string.Format("ClusterOrDom={0} | ValueReject={1} | Reclaim={2}",
                                clusterOrDomPassShort, valueRejectGate, reclaimPassShort);
                            break;
                        }

                        case AdaptiveContextFamily.AboveValueReversal:
                        {
                            bool clusterOrDomPassShort = bearClusterCount >= 2 || domVolShortPercent >= adaptiveProfileShort.MinDomVol;
                            if (!clusterOrDomPassShort)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "AboveVAH: needs bear cluster >= 2 or DomVol support";
                            }

                            bool reversalGateAShort = improvingDeltaShort && (barDelta < 0) && (validBearishRatio >= adaptiveProfileShort.MinRatio);
                            bool reversalGateBShort = (s3_absShortMult >= 2.0) && (escapeShortTicks <= 0);
                            bool reversalProofShort = reversalGateAShort || reversalGateBShort;
                            if (!reversalProofShort)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "AboveVAH: needs negative reclaim proof or absorption reversal";
                            }

                            bool pocDropPassShort = !adaptiveProfileShort.RequirePocLift
                                || ((pocBarsProcessed >= 2) && (pMig1 < 0 || revDown));
                            if (!pocDropPassShort)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "AboveVAH: POC drop required";
                            }

                            bool reclaimPassShort = !adaptiveProfileShort.RequireAvwapReclaim || activeAnchorIdx <= 0 || activeAnchorReclaimed;
                            if (!reclaimPassShort)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "AboveVAH: active AVWAP reclaim required";
                            }

                            matrixProofStateShort = string.Format("ClusterOrDom={0} | GateA={1} | GateB={2} | POCDrop={3} | Reclaim={4}",
                                clusterOrDomPassShort, reversalGateAShort, reversalGateBShort, pocDropPassShort, reclaimPassShort);
                            break;
                        }

                        case AdaptiveContextFamily.WithGrainShortContinuation:
                        {
                            bool domPassShort = domVolShortPercent >= adaptiveProfileShort.MinDomVol;
                            if (!domPassShort)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "ShortCont: DomVol below minimum";
                            }

                            matrixProofStateShort = string.Format("DomPass={0} (Need>={1:F1})", domPassShort, adaptiveProfileShort.MinDomVol);
                            break;
                        }

                        case AdaptiveContextFamily.LowerValueFriction:
                        {
                            bool domPassShort = domVolShortPercent >= adaptiveProfileShort.MinDomVol;
                            if (!domPassShort)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "LowerFriction: DomVol below minimum";
                            }

                            bool ratioPassShort = validBearishRatio >= adaptiveProfileShort.MinRatio;
                            if (!ratioPassShort)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "LowerFriction: ratio below minimum";
                            }

                            bool improvingPassShort = !adaptiveProfileShort.RequireImprovingDelta || improvingDeltaShort;
                            if (!improvingPassShort)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "LowerFriction: improving delta required";
                            }

                            matrixProofStateShort = string.Format("DomPass={0} | RatioPass={1} | ImprovingDelta={2}",
                                domPassShort, ratioPassShort, improvingPassShort);
                            break;
                        }

                        case AdaptiveContextFamily.BasementBreakdown:
                        {
                            bool intensityPassShort = (domVolShortPercent >= adaptiveProfileShort.MinDomVol) || (validBearishRatio >= adaptiveProfileShort.MinRatio);
                            if (!intensityPassShort)
                            {
                                matrixVerdictShort = false;
                                if (string.IsNullOrEmpty(matrixBlockReasonShort))
                                    matrixBlockReasonShort = "BasementBreak: needs DomVol or Ratio breakdown intensity";
                            }

                            matrixProofStateShort = string.Format("IntensityPass={0} (Dom>={1:F1} OR Ratio>={2:F1})",
                                intensityPassShort, adaptiveProfileShort.MinDomVol, adaptiveProfileShort.MinRatio);
                            break;
                        }
                    }

                    if (string.IsNullOrEmpty(matrixProofStateShort))
                        matrixProofStateShort = "No family-specific matrix rules fired";

                    if (matrixVerdictShort && string.IsNullOrEmpty(matrixBlockReasonShort))
                        matrixBlockReasonShort = "PASS";
                }

                bool fullEnginePassShort = preMatrixPassShort && matrixVerdictShort;

                if (UseAdaptiveContextMatrix)
                {
                    if (ShadowMatrixMode)
                        s3_short_valid = preMatrixPassShort;
                    else
                        s3_short_valid = fullEnginePassShort;
                }
                else
                {
                    s3_short_valid = preMatrixPassShort;
                }

                bool validShortSignal = s3_short_valid && CooldownWindowComplete(Time[0]);

                if (validShortSignal)
                {
                    // Capture Entry Snapshot for Short
                    lastEntryContext = stackContextShort;
                    lastEntryVolRegime = volRegime;
                    lastEntryStackRecency = stackRecencyShort;
                    lastEntrySessionPos = sessionPosShort;
                    lastEntryVolZScore = volZScore;
                    lastEntryAdaptiveMinVol = adaptiveMinVol;
                    lastEntryAdaptiveMaxVol = adaptiveMaxVol;
                    lastEntryTimeBaseline = timeBaseline;
                    lastEntryFollowThroughRate = ftRate;
                    lastEntryAvgMfe = ftAvgMfe;
                    lastEntryClusterCount = bearClusterCount;

                    lastEntryAdaptiveVolBase = adaptiveVolumeBaseline;
                    lastEntryAdaptiveVolStdDev = adaptiveVolumeStdDev;
                    lastEntryTotalBarVol = totalBarVol;
                    lastEntryVolumeSpikeRatio = currentVolSpikeRatio;
                    lastEntryTimeAdjMinVol = timeAdjustedMinVol;
                    lastEntryFtSampleCount = ftSampleCount;
                    lastEntryFtAvgMae = ftAvgMae;
                    lastEntryNetCnt = cAdvShort;
                    lastEntryRegimeAllowed = regimeAllowed;
                    lastEntryBaseStackPass = (S3_Enable && maxBearishStack >= S3_MinStackSize && maxBearishStack <= S3_MaxStackSize);
                    lastEntryPreMatrixPass = preMatrixPassShort;
                    lastEntryMatrixVerdict = matrixVerdictShort;

                    lastEntryBarDelta = barDelta;
                    lastEntryNormDeltaPct = normDeltaPct;
                    lastEntryBarDir = barDir;
                    lastEntryPrevBarDelta1 = prevBarDelta1;
                    lastEntryPrevBarDelta2 = prevBarDelta2;
                    lastEntryImprovingDelta = improvingDeltaShort;
                    lastEntryDivLong = divShort;
                    lastEntryPocMig1 = pMig1 / TickSize;
                    lastEntryRevUp = revDown;
                    lastEntryCurrentPoc = currentPocPrice;
                    lastEntryPrevPoc1 = prevPoc1;
                    lastEntryPrevPoc2 = prevPoc2;

                    lastEntryVolRegimeGateAllowed = volRegimeGateAllowed;
                    lastEntryRollingR1k = rollingR1k;
                    lastEntryMicroRegime = GetMicroRegimeString(currentMicroRegime);
                    lastEntrySessionContextGateAllowed = IsSessionContextAllowed(stackContextShortEnum);
                    lastEntryMinSecsPass = passMinBarSecsShort;
                    lastEntryMaxEscapeGlobalPass = passMaxEscapeGlobalShort;
                    lastEntryAdaptive40RangeFilterPass = true;
                    lastEntryESRangeFilterPass = true;

                    lastEntryBarIsClimax = isClimax;
                    lastEntryBarIsExhaustion = isExhaustion;
                    lastEntryPrevBarWasClimax = prevBarClimaxState;
                    lastEntryClimaxScore = climaxScore;
                    lastEntryExhaustionScore = exhaustionScore;
                    lastEntryClimaxPrevVol = priorBarVolumeForTelemetry;
                    lastEntryClimaxCurVol = totalBarVol;
                    lastEntryPassClimaxFilter = passClimaxFilter;
                    lastEntryPassExhaustionFilter = !UseExhaustionFilter || isExhaustion || !RequireExhaustionSetup;

                    lastEntryVAH = nyseSessionVAH;
                    lastEntryVAL = nyseSessionVAL;
                    lastEntrySessionPOCVA = nyseSessionPOC;
                    lastEntryVAContext = vaContextStr;
                    lastEntryPriceDistToPOC = priceDistToPOC;
                    lastEntryPassVAFilter = passVAFilter;

                    lastEntryDeltaROC = currentDeltaROC;
                    lastEntryDeltaAccel = currentDeltaAccel;
                    lastEntryDeltaVelocityScore = deltaVelocityScore;
                    lastEntryDeltaMomentum = GetDeltaMomentumString(currentDeltaMomentum);
                    lastEntryPassDeltaVelocityFilter = passDeltaVelocityFilter;

                    lastEntryOlderSlope = s3_olderSlope;
                    lastEntrySlopeAccel = s3_slopeAccel;
                    lastEntryPassCdAccel = !S3_UseCdSlopeAccel || (s3_slopeAccel <= -S3_MinCdSlopeAccel);
                    lastEntryPassDeltaDiv = !S3_UseDeltaDivergence || (S3_RequireDeceleration ? improvingDeltaShort : divShort);

                    double s3_absShortPctSnap = (totalBarVol > 0) ? (s3_highZoneVol / totalBarVol) * 100.0 : 0;
                    double s3_absShortMultSnap = s3_highAsk / Math.Max(1.0, avgVolPerTick);

                    lastEntryLowZoneVol = s3_highZoneVol;
                    lastEntryLowBid = s3_highAsk;
                    lastEntryLowAsk = s3_highBid;
                    lastEntryAbsPct = s3_absShortPctSnap;
                    lastEntryAbsMult = s3_absShortMultSnap;
                    lastEntryPassAbsorb = !S3_UseAbsorption ||
                                          ((s3_absShortPctSnap >= S3_MinAbsorptionPct) &&
                                           (!S3_UseMaxAbsorption || s3_absShortPctSnap <= S3_MaxAbsorptionPct) &&
                                           (s3_absShortMultSnap >= S3_MinAbsorptionMultiple));
                    lastEntryPassPocMig = !S3_UsePocMigration || ((pocBarsProcessed >= 2) && (!S3_RequirePocReversal || revDown) && (-pMig1 / TickSize >= S3_MinPocMigrationTicks));

                    lastEntryAdaptiveFamily = GetAdaptiveContextFamilyString(adaptiveContextFamilyShort);
                    lastEntryAdaptiveRuleSummary = "";
                    lastEntryMatrixProofState = matrixProofStateShort;
                    lastEntryMatrixBlockReason = matrixBlockReasonShort;
                    lastEntryConstantVolumeMode = constantVolumeBarMode;
                    lastEntryDisableBarVolumeFilters = disableBarVolumeDependentFilters;
                    lastEntrySessionAxis = sessionBucketShortStr;
                    lastEntrySpatialPair = spatialPairShortStr;

                    lastEntrySignalPrice = Close[1];
                    lastEntrySessionHigh = sessionHigh;
                    lastEntrySessionLow = sessionLow;
                    lastEntrySessionMid = signalSessionMid;
                    lastEntrySignalBarRangeTicks = signalBarRangeTicks;
                    lastEntrySignalBarSecs = signalBarSecs;
                    lastEntryRangePer1kVolumeTicks = rangePer1kVolumeTicks;
                    lastEntryDeltaPerTick = deltaPerTick;
                    lastEntryDeltaPctOfVolume = deltaPctOfVolume;
                    lastEntryImbalanceDensity = imbalanceDensity;
                    lastEntryPocVolPct = pocVolPct;
                    lastEntryMaxVolAtPrice = maxVolAtPrice;
                    lastEntryUpperZoneVol = s3_lowZoneVol;
                    lastEntryUpperZonePct = lowZonePct;
                    lastEntryLowZonePct = highZonePct;
                    lastEntryBullishImbalanceCount = bullishImbalanceCount;
                    lastEntryBearishImbalanceCount = bearishImbalanceCount;
                    lastEntryMaxBullishStack = maxBullishStack;
                    lastEntryMaxBearishStack = maxBearishStack;
                    lastEntryEscapeTicks = escapeShortTicks;
                    lastEntryDomVolPercent = domVolShortPercent;
                    lastEntryValidBullishRatio = validBearishRatio == double.MaxValue ? 999.0 : validBearishRatio;
                    lastEntryPocPosition = pocPosition;
                    lastEntryRangeBarMode = rangeBarMode;
                    lastEntryRangePace = rangePaceLabel;
                    lastEntryRangeClosePos = signalClosePosPct;
                    lastEntryRangeBodyPct = signalBodyPct;
                    lastEntryRangeOverlapPct = signalOverlapPct;
                    lastEntryRangeLowerWickPct = signalLowerWickPct;
                    lastEntryRangeUpperWickPct = signalUpperWickPct;
                    lastEntryPriceToSessionLowTicks = priceToSessionLowTicks;
                    lastEntryPriceToSessionHighTicks = priceToSessionHighTicks;
                    lastEntryPriceToSessionMidTicks = priceToSessionMidTicks;
                    lastEntryPriceToVALTicks = priceToVALTicks;
                    lastEntryPriceToVAHTicks = priceToVAHTicks;
                    lastEntryPriceToPOCSignedTicks = priceToPOCSignedTicks;
                    lastEntryKeyLevelSummary = keyLevelSummary;
                    lastEntryNearestKeyLevel = nearestKeyLevel;
                    lastEntryNearestKeyLevelDistTicks = nearestKeyLevelAbsTicks == double.MaxValue ? 0 : nearestKeyLevelAbsTicks;
                    lastEntryNearVWAP = nearVWAP;
                    lastEntryNearPDH = nearPDH;
                    lastEntryNearPDL = nearPDL;
                    lastEntryNearIBH = nearIBH;
                    lastEntryNearIBL = nearIBL;
                    lastEntryNearPMH = nearPMH;
                    lastEntryNearPML = nearPML;
                    lastEntryNearPOC = nearPOC;
                    lastEntryKeyLevelGatePass = keyLevelGatePass;

                    // Build Short Trade Log
                    string localTradeLogShort = "";
                    if (UseTradeLogging)
                    {
                        double logRatioShort = validBearishRatio == double.MaxValue ? 999.0 : validBearishRatio;

                        var logSbShort = new StringBuilder();
                        logSbShort.AppendFormat("SigBar: {0} | Entry: {{ENTRY_TIME}} | SHORT (TIER A SHORT) | SigPx: {1} | Dir: {2} | ",
                            Time[1].ToString("yyyy-MM-dd HH:mm:ss"), Close[1], barDir);
                        logSbShort.AppendFormat("BarDelta: {0:F0} | Stack: {1} (Pos: {2:F2} | Ratio: {3:F1} | OppStack: {4}) | ",
                            barDelta, maxBearishStack, stackPosShort, logRatioShort, maxBullishStack);
                        logSbShort.AppendFormat("ImbVol: {0:F1} | Vol: {1} | POC: {2:F2} (PocVol: {3:F0} / {4:F1}%) | ",
                            validAvgBearishImbVol, totalBarVol, pocPosition, maxVolAtPrice, pocVolPct);
                        logSbShort.AppendFormat("CvdState: {0} (Allowed: {1}) | ImbCount: [{2}B/{3}S/NetCnt: {4}/NetD: {5:+0;-0;0}] | Escape: {6:F0}T | ",
                            stateNameStr, regimeAllowed, bullishImbalanceCount, bearishImbalanceCount, cAdvShort, dAdvShort, escapeShortTicks);
                        logSbShort.AppendFormat("DomVol: {0:F1}% | CD Slope: {1:F2}% | CtxFam: {2} | Pair: {3} | KeyLvl: {4} | SigRange: {5:F1}T | SigSecs: {6:F2} | R1k: {7:F1}T | D/V: {8:F1}%",
                            domVolShortPercent, cdSlopeLog_S3_Long, GetAdaptiveContextFamilyString(adaptiveContextFamilyShort), spatialPairShortStr, nearestKeyLevel, signalBarRangeTicks, signalBarSecs, rangePer1kVolumeTicks, deltaPctOfVolume);

                        localTradeLogShort = logSbShort.ToString();
                    }

                    pendingTradeLog = localTradeLogShort.Replace("{ENTRY_TIME}", Time[0].ToString("yyyy-MM-dd HH:mm:ss"));

                    CaptureAnchorAvwapTelemetry(
                        vBarsType, rthOpenBarIdx, hasReclaimedOpenVwap,
                        out lastEntryAvwapOpen, out lastEntryAvwapOpenHistorical, out lastEntryAvwapOpenSignalDistTicks,
                        out lastEntryAvwapOpenSlopeDropTicks, out lastEntryAvwapOpenTier, out lastEntryAvwapOpenSlope, out lastEntryAvwapOpenReclaimed);

                    CaptureAnchorAvwapTelemetry(
                        vBarsType, sessionHighBarIdx, hasReclaimedHighVwap,
                        out lastEntryAvwapHigh, out lastEntryAvwapHighHistorical, out lastEntryAvwapHighSignalDistTicks,
                        out lastEntryAvwapHighSlopeDropTicks, out lastEntryAvwapHighTier, out lastEntryAvwapHighSlope, out lastEntryAvwapHighReclaimed);

                    CaptureAnchorAvwapTelemetry(
                        vBarsType, sessionLowBarIdx, hasReclaimedLowVwap,
                        out lastEntryAvwapLow, out lastEntryAvwapLowHistorical, out lastEntryAvwapLowSignalDistTicks,
                        out lastEntryAvwapLowSlopeDropTicks, out lastEntryAvwapLowTier, out lastEntryAvwapLowSlope, out lastEntryAvwapLowReclaimed);

                    lastEntryAvwapActiveAnchor = "N/A";
                    lastEntryAvwapTier = "N/A";
                    lastEntryAvwapSlope = "N/A";
                    lastEntryAvwapSlopeDropTicks = 0;
                    lastEntryAvwapSignalDistTicks = 0;
                    lastEntryAvwapReclaimed = false;

                    switch (AvwapAnchor)
                    {
                        case AvwapAnchorType.SessionOpen:
                            lastEntryAvwapActiveAnchor = "OPEN";
                            lastEntryAvwapTier = lastEntryAvwapOpenTier;
                            lastEntryAvwapSlope = lastEntryAvwapOpenSlope;
                            lastEntryAvwapSlopeDropTicks = lastEntryAvwapOpenSlopeDropTicks;
                            lastEntryAvwapSignalDistTicks = lastEntryAvwapOpenSignalDistTicks;
                            lastEntryAvwapReclaimed = lastEntryAvwapOpenReclaimed;
                            break;
                        case AvwapAnchorType.SessionHigh:
                            lastEntryAvwapActiveAnchor = "HIGH";
                            lastEntryAvwapTier = lastEntryAvwapHighTier;
                            lastEntryAvwapSlope = lastEntryAvwapHighSlope;
                            lastEntryAvwapSlopeDropTicks = lastEntryAvwapHighSlopeDropTicks;
                            lastEntryAvwapSignalDistTicks = lastEntryAvwapHighSignalDistTicks;
                            lastEntryAvwapReclaimed = lastEntryAvwapHighReclaimed;
                            break;
                        case AvwapAnchorType.SessionLow:
                            lastEntryAvwapActiveAnchor = "LOW";
                            lastEntryAvwapTier = lastEntryAvwapLowTier;
                            lastEntryAvwapSlope = lastEntryAvwapLowSlope;
                            lastEntryAvwapSlopeDropTicks = lastEntryAvwapLowSlopeDropTicks;
                            lastEntryAvwapSignalDistTicks = lastEntryAvwapLowSignalDistTicks;
                            lastEntryAvwapReclaimed = lastEntryAvwapLowReclaimed;
                            break;
                    }

                    if (UseTradeLogging)
                        Print(string.Format("Immediate Short Entry | EntryBar={0:yyyy-MM-dd HH:mm:ss} | B1={1:HH:mm:ss} O1={2} C1={3}",
                            Time[0], Time[1], Open[1], Close[1]));

                    double currentBidShort = GetCurrentBid();
                    double currentAskShort = GetCurrentAsk();
                    double currentSpreadShort = (currentAskShort > 0 && currentBidShort > 0) ? (currentAskShort - currentBidShort) / TickSize : 0;
                    lastEntrySignalSpread = currentSpreadShort;
                    lastEntryAvgSpread = barSpreadCount > 0 ? barSpreadSum / barSpreadCount : currentSpreadShort;
                    lastEntryMaxSpread = barSpreadCount > 0 ? barSpreadMax : currentSpreadShort;
                    lastEntryBookBidVol = 0;
                    lastEntryBookAskVol = 0;

                    EnterShort("MomSE");
                }
            }
            #endregion

            #region POC History Update
            if (totalBarVol > 0)
            {
                prevPoc2 = prevPoc1;
                prevPoc1 = currentPocPrice;
                pocBarsProcessed++;
            }
            #endregion
        }
        #endregion

        #region Properties
        // ==============================================================================
        // 00-03: GLOBAL SETTINGS
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "Allow Long Trades", Order = 1, GroupName = "00. GLOBAL: Direction")]
        public bool AllowLongTrades { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Short Trades", Order = 2, GroupName = "00. GLOBAL: Direction")]
        public bool AllowShortTrades { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow BULL-DIV Trades", Order = 1, GroupName = "00b. GLOBAL: Allowed Regimes")]
        public bool AllowBullDiv { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow BEAR-DIV Trades", Order = 2, GroupName = "00b. GLOBAL: Allowed Regimes")]
        public bool AllowBearDiv { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow BULL-CONV Trades", Order = 3, GroupName = "00b. GLOBAL: Allowed Regimes")]
        public bool AllowBullConv { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow BEAR-CONV Trades", Order = 4, GroupName = "00b. GLOBAL: Allowed Regimes")]
        public bool AllowBearConv { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Use Cooldown", Order = 1, GroupName = "01. GLOBAL: Cooldown")]
        public bool UseCooldown { get; set; }

        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "Cooldown (Minutes)", Order = 2, GroupName = "01. GLOBAL: Cooldown")]
        public int CooldownMinutes { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Use Diagonal Imbalance", Order = 1, GroupName = "02. GLOBAL: Imbalance Core")]
        public bool UseDiagonalImbalance { get; set; }

        [NinjaScriptProperty]
        [Range(1.0, 50.0)]
        [Display(Name = "Imbalance Ratio", Order = 2, GroupName = "02. GLOBAL: Imbalance Core")]
        public double ImbalanceRatio { get; set; }

        [NinjaScriptProperty]
        [Range(1.0, 999.0)]
        [Display(Name = "Max Imbalance Ratio", Order = 3, GroupName = "02. GLOBAL: Imbalance Core")]
        public double MaxImbalanceRatio { get; set; }

        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "Min Volume Per Imbalance", Order = 4, GroupName = "02. GLOBAL: Imbalance Core")]
        public int MinImbalanceVolume { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Edge Handling Mode", Order = 5, GroupName = "02. GLOBAL: Imbalance Core")]
        public ImbalanceEdgeHandlingMode EdgeHandlingMode { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Infinite Edge Ratio", Order = 6, GroupName = "02. GLOBAL: Imbalance Core")]
        public bool AllowInfiniteEdgeRatio { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Reset Adaptive Buffers Daily", Order = 7, GroupName = "02. GLOBAL: Imbalance Core")]
        public bool ResetAdaptiveOnDayTransition { get; set; }

        // ==============================================================================
        // 03b: VOLATILITY REGIME GATE
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "Use Volatility Regime Gate", Order = 1, GroupName = "03b. VOLATILITY REGIME GATE")]
        public bool UseVolatilityRegimeGate { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow DEAD Regime", Order = 2, GroupName = "03b. VOLATILITY REGIME GATE")]
        public bool AllowDeadRegime { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow QUIET Regime", Order = 3, GroupName = "03b. VOLATILITY REGIME GATE")]
        public bool AllowQuietRegime { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow NORMAL Regime", Order = 4, GroupName = "03b. VOLATILITY REGIME GATE")]
        public bool AllowNormalRegime { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow ACTIVE Regime", Order = 5, GroupName = "03b. VOLATILITY REGIME GATE")]
        public bool AllowActiveRegime { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow EXTREME Regime", Order = 6, GroupName = "03b. VOLATILITY REGIME GATE")]
        public bool AllowExtremeRegime { get; set; }

        // ==============================================================================
        // 03c: CLIMAX/EXHAUSTION FILTER
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "Use Climax Filter", Order = 1, GroupName = "03c. CLIMAX/EXHAUSTION FILTER")]
        public bool UseClimaxFilter { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Block Entry ON Climax Bar", Order = 2, GroupName = "03c. CLIMAX/EXHAUSTION FILTER")]
        public bool BlockEntryOnClimaxBar { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Require Post-Climax Entry", Order = 3, GroupName = "03c. CLIMAX/EXHAUSTION FILTER")]
        public bool RequirePostClimaxEntry { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Use Exhaustion Filter", Order = 4, GroupName = "03c. CLIMAX/EXHAUSTION FILTER")]
        public bool UseExhaustionFilter { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Require Exhaustion Setup", Order = 5, GroupName = "03c. CLIMAX/EXHAUSTION FILTER")]
        public bool RequireExhaustionSetup { get; set; }

        // ==============================================================================
        // 03c-2: ADAPTIVE 40 RANGE FILTER
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "01. Use Adaptive 40 Range Filter", Order = 1, GroupName = "03c-2. ADAPTIVE 40 RANGE")]
        public bool UseAdaptive40RangeFilter { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "02. Block LOWER-CONT + ACCEL-BUY", Order = 2, GroupName = "03c-2. ADAPTIVE 40 RANGE")]
        public bool Block_LowerCont_AccelBuy { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "03. Block MID-RANGE + ACCEL-BUY", Order = 3, GroupName = "03c-2. ADAPTIVE 40 RANGE")]
        public bool Block_MidRange_AccelBuy { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "04. Block NIC = 1", Order = 4, GroupName = "03c-2. ADAPTIVE 40 RANGE")]
        public bool Block_NIC1 { get; set; }

        // ==============================================================================
        // 03c-3: ES 8-RANGE FILTER
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "01. Use ES 8-Range Filter", Order = 1, GroupName = "03c-3. ES 8-RANGE FILTER")]
        public bool UseESRangeFilter { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "02. Block SESS-HIGH-BO + ACCEL-BUY (F1)", Order = 2, GroupName = "03c-3. ES 8-RANGE FILTER")]
        public bool ES_Block_HighBO_AccelBuy { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "03. Block UPPER-FRICTION + QUIET + ACCEL-BUY (F4)", Order = 3, GroupName = "03c-3. ES 8-RANGE FILTER")]
        public bool ES_Block_UpperFriction_Quiet_AccelBuy { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "04. Block AVWAP EXTREME Tier (F5)", Order = 4, GroupName = "03c-3. ES 8-RANGE FILTER")]
        public bool ES_Block_AvwapExtreme { get; set; }

        // ==============================================================================
        // 03c-4: PHASE 1 BLOCKING RULES
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "01. Block SESS-LOW-REV (Phase1 Rule #1)", Order = 1, GroupName = "03c-4. PHASE 1 BLOCKING RULES")]
        public bool BlockSessLowRev { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "02. Block SESS-HIGH-BO + ACTIVE + ABOVE-VAH (Phase1 Rule #2)", Order = 2, GroupName = "03c-4. PHASE 1 BLOCKING RULES")]
        public bool BlockCeilingActiveAboveVAH { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "03. Block LOWER-CONT + BELOW-VAL + NORMAL/QUIET (W2 Rule B)", Order = 3, GroupName = "03c-4. PHASE 1 BLOCKING RULES")]
        public bool BlockLowerContBelowValLowVol { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "04. Block SESS-HIGH-BO + AT-VAH (W2 Rule C)", Order = 4, GroupName = "03c-4. PHASE 1 BLOCKING RULES")]
        public bool BlockCeilingAtVAH { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "05. Block LOWER-CONT + Cluster>=2 (W2 Rule F)", Order = 5, GroupName = "03c-4. PHASE 1 BLOCKING RULES")]
        public bool BlockLowerContCluster2 { get; set; }

        // ==============================================================================
        // 03d: VALUE AREA FILTER
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "01. Use Value Area Filter", Order = 1, GroupName = "03d. VALUE AREA FILTER (NYSE 9:30-4PM)")]
        public bool UseValueAreaFilter { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "02. Allow Trades at NO-VA", Order = 2, GroupName = "03d. VALUE AREA FILTER (NYSE 9:30-4PM)")]
        public bool VA_AllowNoVA { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "03. Allow Trades BELOW-VAL", Order = 3, GroupName = "03d. VALUE AREA FILTER (NYSE 9:30-4PM)")]
        public bool VA_AllowBelowVAL { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "04. Allow Trades AT-VAL", Order = 4, GroupName = "03d. VALUE AREA FILTER (NYSE 9:30-4PM)")]
        public bool VA_AllowAtVAL { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "05. Allow Trades IN-VALUE", Order = 5, GroupName = "03d. VALUE AREA FILTER (NYSE 9:30-4PM)")]
        public bool VA_AllowInValue { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "06. Allow Trades AT-POC", Order = 6, GroupName = "03d. VALUE AREA FILTER (NYSE 9:30-4PM)")]
        public bool VA_AllowAtPOC { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "07. Allow Trades AT-VAH", Order = 7, GroupName = "03d. VALUE AREA FILTER (NYSE 9:30-4PM)")]
        public bool VA_AllowAtVAH { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "08. Allow Trades ABOVE-VAH", Order = 8, GroupName = "03d. VALUE AREA FILTER (NYSE 9:30-4PM)")]
        public bool VA_AllowAboveVAH { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "09. Require Recent POC Touch", Order = 9, GroupName = "03d. VALUE AREA FILTER (NYSE 9:30-4PM)")]
        public bool VA_RequirePOCTouch { get; set; }

        [NinjaScriptProperty]
        [Range(1, 50)]
        [Display(Name = "10. POC Touch Lookback Bars", Order = 10, GroupName = "03d. VALUE AREA FILTER (NYSE 9:30-4PM)")]
        public int VA_POCTouchLookbackBars { get; set; }

        // ==============================================================================
        // 03e: DELTA VELOCITY FILTER
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "Use Delta Velocity Filter", Order = 1, GroupName = "03e. DELTA VELOCITY FILTER")]
        public bool UseDeltaVelocityFilter { get; set; }

        [NinjaScriptProperty]
        [Range(3, 20)]
        [Display(Name = "Delta Velocity Lookback", Order = 2, GroupName = "03e. DELTA VELOCITY FILTER")]
        public int DeltaVelocityLookback { get; set; }

        [NinjaScriptProperty]
        [Range(-500.0, 500.0)]
        [Display(Name = "Min Delta ROC", Order = 3, GroupName = "03e. DELTA VELOCITY FILTER")]
        public double DV_MinDeltaROC { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Require Positive Acceleration", Order = 4, GroupName = "03e. DELTA VELOCITY FILTER")]
        public bool DV_RequirePositiveAccel { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Block Accelerating Selling", Order = 5, GroupName = "03e. DELTA VELOCITY FILTER")]
        public bool DV_BlockAcceleratingSelling { get; set; }

        // ==============================================================================
        // 03f: ADAPTIVE / PERFORMANCE GATES
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "Use Adaptive Volume Gate", Order = 1, GroupName = "03f. ADAPTIVE / PERFORMANCE GATES")]
        public bool UseAdaptiveVolumeGate { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 5.0)]
        [Display(Name = "Adaptive Min Volume Mult", Order = 2, GroupName = "03f. ADAPTIVE / PERFORMANCE GATES")]
        public double AdaptiveVolumeMinMultiplier { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 10.0)]
        [Display(Name = "Adaptive Max Volume StdDev Mult", Order = 3, GroupName = "03f. ADAPTIVE / PERFORMANCE GATES")]
        public double AdaptiveVolumeMaxStdDevMultiplier { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Use Time-Adjusted Volume Gate", Order = 4, GroupName = "03f. ADAPTIVE / PERFORMANCE GATES")]
        public bool UseTimeAdjustedVolumeGate { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 5.0)]
        [Display(Name = "Time-Adjusted Min Volume Mult", Order = 5, GroupName = "03f. ADAPTIVE / PERFORMANCE GATES")]
        public double TimeAdjustedVolumeMinMultiplier { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Use Follow-Through Gate", Order = 6, GroupName = "03f. ADAPTIVE / PERFORMANCE GATES")]
        public bool UseFollowThroughGate { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 1.0)]
        [Display(Name = "Follow-Through Min Rate", Order = 7, GroupName = "03f. ADAPTIVE / PERFORMANCE GATES")]
        public double FollowThroughMinRate { get; set; }

        [NinjaScriptProperty]
        [Range(1, 100)]
        [Display(Name = "Follow-Through Min Samples", Order = 8, GroupName = "03f. ADAPTIVE / PERFORMANCE GATES")]
        public int FollowThroughMinSamples { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 200.0)]
        [Display(Name = "Follow-Through Success MFE (Ticks)", Order = 9, GroupName = "03f. ADAPTIVE / PERFORMANCE GATES")]
        public double FollowThroughMinTicks { get; set; }

        // ==============================================================================
        // 03g: MICROSTRUCTURE REGIME FILTER
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "Enable Regime Filter", Order = 1, GroupName = "03g. MICROSTRUCTURE REGIME FILTER")]
        public bool EnableRegimeFilter { get; set; }

        [NinjaScriptProperty]
        [Range(5, 100)]
        [Display(Name = "R1k Rolling Window (Bars)", Order = 2, GroupName = "03g. MICROSTRUCTURE REGIME FILTER")]
        public int R1kRollingWindowBars { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 10000.0)]
        [Display(Name = "Dense Threshold (R1k <)", Order = 3, GroupName = "03g. MICROSTRUCTURE REGIME FILTER")]
        public double RegimeDenseThreshold { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 10000.0)]
        [Display(Name = "Thin Threshold (R1k >)", Order = 4, GroupName = "03g. MICROSTRUCTURE REGIME FILTER")]
        public double RegimeThinThreshold { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Dense Regime", Order = 5, GroupName = "03g. MICROSTRUCTURE REGIME FILTER")]
        public bool AllowDenseRegime { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Normal Regime", Order = 6, GroupName = "03g. MICROSTRUCTURE REGIME FILTER")]
        public bool AllowNormalMicroRegime { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Thin Regime", Order = 7, GroupName = "03g. MICROSTRUCTURE REGIME FILTER")]
        public bool AllowThinRegime { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Warmup Regime", Order = 8, GroupName = "03g. MICROSTRUCTURE REGIME FILTER")]
        public bool AllowWarmupRegime { get; set; }

        // ==============================================================================
        // 03h: ANCHORED VWAP FILTER (4-Tier Engine)
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "1. Use AVWAP Filter", Order = 1, GroupName = "03h. ANCHORED VWAP FILTER")]
        public bool UseAvwapFilter { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "2. Anchor To", Order = 2, GroupName = "03h. ANCHORED VWAP FILTER")]
        public AvwapAnchorType AvwapAnchor { get; set; }

        [NinjaScriptProperty]
        [Range(0, 500)]
        [Display(Name = "3. Deadzone Max Ticks", Order = 3, GroupName = "03h. ANCHORED VWAP FILTER")]
        public int AvwapDeadzoneTicks { get; set; }

        [NinjaScriptProperty]
        [Range(1, 1000)]
        [Display(Name = "4. Extreme Zone Min Ticks", Order = 4, GroupName = "03h. ANCHORED VWAP FILTER")]
        public int AvwapExtremeTicks { get; set; }

        [NinjaScriptProperty]
        [Range(1, 2000)]
        [Display(Name = "5. Killzone Min Ticks", Order = 5, GroupName = "03h. ANCHORED VWAP FILTER")]
        public int AvwapKillzoneTicks { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "6. Use Slope Acceptance Filter", Order = 6, GroupName = "03h. ANCHORED VWAP FILTER")]
        public bool UseAvwapSlopeFilter { get; set; }

        [NinjaScriptProperty]
        [Range(1, 50)]
        [Display(Name = "7. Slope Lookback Bars", Order = 7, GroupName = "03h. ANCHORED VWAP FILTER")]
        public int AvwapSlopeLookbackBars { get; set; }

        [NinjaScriptProperty]
        [Range(0, 100)]
        [Display(Name = "7b. Slope Veto Min Drop (Ticks)", Order = 8, GroupName = "03h. ANCHORED VWAP FILTER")]
        public int AvwapSlopeVetoTicks { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "8. Use VWAP Acceptance Filter (Since 9:30)", Order = 9, GroupName = "03h. ANCHORED VWAP FILTER")]
        public bool UseVwapAcceptanceFilter { get; set; }

        // ==============================================================================
        // 03i: SESSION CONTEXT FILTER
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "01. Use Session Context Filter", Order = 1, GroupName = "03i. SESSION CONTEXT FILTER")]
        public bool UseSessionContextFilter { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "02. Allow SESS-LOW-REV (0.0-0.2)", Order = 2, GroupName = "03i. SESSION CONTEXT FILTER")]
        public bool Session_AllowLowRev { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "03. Allow LOWER-CONT (0.2-0.4)", Order = 3, GroupName = "03i. SESSION CONTEXT FILTER")]
        public bool Session_AllowLowerCont { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "04. Allow MID-RANGE (0.4-0.6)", Order = 4, GroupName = "03i. SESSION CONTEXT FILTER")]
        public bool Session_AllowMidRange { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "05. Allow UPPER-CONT (0.6-0.8)", Order = 5, GroupName = "03i. SESSION CONTEXT FILTER")]
        public bool Session_AllowUpperCont { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "06. Allow SESS-HIGH-BO (0.8-1.0)", Order = 6, GroupName = "03i. SESSION CONTEXT FILTER")]
        public bool Session_AllowHighBo { get; set; }

        // ==============================================================================
        // 03i-b: SIGNAL QUALITY GLOBAL FILTERS
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "01. Use Min Signal Bar Duration", Order = 1, GroupName = "03l. SIGNAL BAR QUALITY")]
        public bool UseMinBarSecs { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 300.0)]
        [Display(Name = "02. Min Signal Bar Duration (Secs)", Order = 2, GroupName = "03l. SIGNAL BAR QUALITY")]
        public double MinBarSecsThreshold { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "03. Use Max Escape Ticks Global", Order = 3, GroupName = "03l. SIGNAL BAR QUALITY")]
        public bool UseMaxEscapeGlobal { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 200.0)]
        [Display(Name = "04. Max Escape Ticks Global", Order = 4, GroupName = "03l. SIGNAL BAR QUALITY")]
        public double MaxEscapeGlobalTicks { get; set; }

        // ==============================================================================
        // 03j: ADAPTIVE CONTEXT MATRIX
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "01. Use Adaptive Context Matrix", Order = 1, GroupName = "03j. ADAPTIVE CONTEXT MATRIX")]
        public bool UseAdaptiveContextMatrix { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "02. Auto Disable Bar-Volume Gates On Constant-Volume Bars", Order = 2, GroupName = "03j. ADAPTIVE CONTEXT MATRIX")]
        public bool AutoDisableBarVolumeFiltersOnConstantVolume { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "03. Enable Shadow Matrix Mode (Log Only, No Blocking)", Order = 3, GroupName = "03j. ADAPTIVE CONTEXT MATRIX")]
        public bool ShadowMatrixMode { get; set; }

        // ==============================================================================
        // 03k: RANGE BAR ADAPTATION
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "01. Use Range-Bar Adaptation", Order = 1, GroupName = "03k. RANGE BAR ADAPTATION")]
        public bool UseRangeBarAdaptation { get; set; }

        [NinjaScriptProperty]
        [Range(1.0, 600.0)]
        [Display(Name = "02. Fast Bar Threshold (Secs)", Order = 2, GroupName = "03k. RANGE BAR ADAPTATION")]
        public double RangeFastBarSecsThreshold { get; set; }

        [NinjaScriptProperty]
        [Range(1.0, 600.0)]
        [Display(Name = "03. Slow Bar Threshold (Secs)", Order = 3, GroupName = "03k. RANGE BAR ADAPTATION")]
        public double RangeSlowBarSecsThreshold { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 1.0)]
        [Display(Name = "04. Min Continuation Close %", Order = 4, GroupName = "03k. RANGE BAR ADAPTATION")]
        public double RangeContinuationCloseMinPct { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 1.0)]
        [Display(Name = "05. Min Strong Slow-Bar Close %", Order = 5, GroupName = "03k. RANGE BAR ADAPTATION")]
        public double RangeStrongSlowBarCloseMinPct { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 1.0)]
        [Display(Name = "06. Max Prior-Bar Overlap %", Order = 6, GroupName = "03k. RANGE BAR ADAPTATION")]
        public double RangeMaxOverlapPct { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 1.0)]
        [Display(Name = "07. Min Rejection Wick %", Order = 7, GroupName = "03k. RANGE BAR ADAPTATION")]
        public double RangeMinRejectionWickPct { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public double AdaptiveBasementMinDomVol { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public double AdaptiveBasementMinEscape { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public bool AdaptiveBasementRequireDeltaImprovement { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public double AdaptiveContinuationMinDomVol { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public double AdaptiveCeilingMinDomVol { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public double AdaptiveCeilingMinRatio { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public double AdaptiveCeilingMinEscape { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public double AdaptiveCeilingMaxEscape { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 100.0)]
        [Display(Name = "12. Ceiling Trap Absorption %", Order = 12, GroupName = "03j. ADAPTIVE CONTEXT MATRIX")]
        public double AdaptiveCeilingTrapAbsorptionPct { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public double AdaptiveMidRangeMinDomVol { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public double AdaptiveMidRangeMinRatio { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public double AdaptiveMidRangeMinEscape { get; set; }

        [Browsable(false)]
        [XmlIgnore]
        public double AdaptiveMidRangeMaxEscape { get; set; }

        // ==============================================================================
        // 04: TIER A PROFILE
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "01. Enable Tier A", Order = 1, GroupName = "04. TIER A PROFILE")]
        public bool S3_Enable { get; set; }

        [NinjaScriptProperty]
        [Range(1, 20)]
        [Display(Name = "02. Min Stack Size", Order = 2, GroupName = "04. TIER A PROFILE")]
        public int S3_MinStackSize { get; set; }

        [NinjaScriptProperty]
        [Range(1, 20)]
        [Display(Name = "03. Max Stack Size", Order = 3, GroupName = "04. TIER A PROFILE")]
        public int S3_MaxStackSize { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "04a. Use Total Bull Count", Order = 4, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseBullCount { get; set; }

        [NinjaScriptProperty]
        [Range(0, 50)]
        [Display(Name = "04b. Min Total Bull Count", Order = 5, GroupName = "04. TIER A PROFILE")]
        public int S3_MinBullCount { get; set; }

        [NinjaScriptProperty]
        [Range(1, 50)]
        [Display(Name = "04c. Max Total Bull Count", Order = 6, GroupName = "04. TIER A PROFILE")]
        public int S3_MaxBullCount { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "05. Use CD Slope", Order = 7, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseCdSlope { get; set; }

        [NinjaScriptProperty]
        [Range(-100.0, 100.0)]
        [Display(Name = "06. Min CD Slope (%)", Order = 8, GroupName = "04. TIER A PROFILE")]
        public double S3_MinCdSlope { get; set; }

        [NinjaScriptProperty]
        [Range(-100.0, 100.0)]
        [Display(Name = "07. Max CD Slope (%)", Order = 9, GroupName = "04. TIER A PROFILE")]
        public double S3_MaxCdSlope { get; set; }

        [NinjaScriptProperty]
        [Range(1, 100)]
        [Display(Name = "08. CD Slope Lookback", Order = 10, GroupName = "04. TIER A PROFILE")]
        public int S3_CdLookback { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "09. Require Div State", Order = 11, GroupName = "04. TIER A PROFILE")]
        public bool S3_RequireDivergence { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "10. Use Min Volume", Order = 12, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseMinVolume { get; set; }

        [NinjaScriptProperty]
        [Range(1, 10000)]
        [Display(Name = "11. Min Bar Volume", Order = 13, GroupName = "04. TIER A PROFILE")]
        public int S3_MinVolume { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "12a. Use Max Volume", Order = 14, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseMaxVolume { get; set; }

        [NinjaScriptProperty]
        [Range(1, 10000)]
        [Display(Name = "12b. Max Bar Volume", Order = 15, GroupName = "04. TIER A PROFILE")]
        public int S3_MaxVolume { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "12c. Use Volume Spike Filter", Order = 16, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseVolumeSpike { get; set; }

        [NinjaScriptProperty]
        [Range(1, 100)]
        [Display(Name = "12d. Vol Spike Lookback", Order = 17, GroupName = "04. TIER A PROFILE")]
        public int S3_VolumeSpikeLookback { get; set; }

        [NinjaScriptProperty]
        [Range(0.1, 100.0)]
        [Display(Name = "12e. Min Vol Spike Ratio", Order = 18, GroupName = "04. TIER A PROFILE")]
        public double S3_MinVolumeSpikeRatio { get; set; }

        [NinjaScriptProperty]
        [Range(0.1, 100.0)]
        [Display(Name = "12f. Max Vol Spike Ratio", Order = 19, GroupName = "04. TIER A PROFILE")]
        public double S3_MaxVolumeSpikeRatio { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "13. Use Max Imb Vol", Order = 20, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseMaxImbVol { get; set; }

        [NinjaScriptProperty]
        [Range(1.0, 500.0)]
        [Display(Name = "14. Max Imbalance Vol", Order = 21, GroupName = "04. TIER A PROFILE")]
        public double S3_MaxImbVol { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "15. Use Dominance", Order = 22, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseDominance { get; set; }

        [NinjaScriptProperty]
        [Range(0, 20)]
        [Display(Name = "16. Min Dom Count", Order = 23, GroupName = "04. TIER A PROFILE")]
        public int S3_MinDomCount { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 1000.0)]
        [Display(Name = "17. Min Dom Delta", Order = 24, GroupName = "04. TIER A PROFILE")]
        public double S3_MinDomDelta { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "18a. Use Min POC Pos", Order = 25, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseMinPoc { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 1.0)]
        [Display(Name = "18b. Min POC Pos", Order = 26, GroupName = "04. TIER A PROFILE")]
        public double S3_MinPoc { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "19a. Use Max POC Pos", Order = 27, GroupName = "04. TIER A PROFILE")]
        public bool S3_UsePoc { get; set; }

        [NinjaScriptProperty]
        [Range(0.01, 1.0)]
        [Display(Name = "19b. Max POC Pos", Order = 28, GroupName = "04. TIER A PROFILE")]
        public double S3_MaxPoc { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "20. Use Min Escape", Order = 29, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseMinEscape { get; set; }

        [NinjaScriptProperty]
        [Range(-50, 50)]
        [Display(Name = "21. Min Escape Ticks", Order = 30, GroupName = "04. TIER A PROFILE")]
        public int S3_MinEscape { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "22. Use Max Escape", Order = 31, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseMaxEscape { get; set; }

        [NinjaScriptProperty]
        [Range(1, 50)]
        [Display(Name = "23. Max Escape Ticks", Order = 32, GroupName = "04. TIER A PROFILE")]
        public int S3_MaxEscape { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "24. Use Min Dom Vol %", Order = 33, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseMinDomVol { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 100.0)]
        [Display(Name = "25. Min Dom Vol %", Order = 34, GroupName = "04. TIER A PROFILE")]
        public double S3_MinDomVol { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "26. Use Max Dom Vol %", Order = 35, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseMaxDomVol { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 100.0)]
        [Display(Name = "27. Max Dom Vol %", Order = 36, GroupName = "04. TIER A PROFILE")]
        public double S3_MaxDomVol { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "28. Use Bar Delta", Order = 37, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseBarDelta { get; set; }

        [NinjaScriptProperty]
        [Range(-2000.0, 2000.0)]
        [Display(Name = "29a. Min Bar Delta", Order = 38, GroupName = "04. TIER A PROFILE")]
        public double S3_MinBarDelta { get; set; }

        [NinjaScriptProperty]
        [Range(-2000.0, 2000.0)]
        [Display(Name = "29b. Max Bar Delta", Order = 39, GroupName = "04. TIER A PROFILE")]
        public double S3_MaxBarDelta { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "30a. Use Normalized Delta %", Order = 40, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseNormalizedDelta { get; set; }

        [NinjaScriptProperty]
        [Range(-100.0, 100.0)]
        [Display(Name = "30b. Min Normalized Delta %", Order = 41, GroupName = "04. TIER A PROFILE")]
        public double S3_MinNormalizedDeltaPct { get; set; }

        [NinjaScriptProperty]
        [Range(-100.0, 100.0)]
        [Display(Name = "30c. Max Normalized Delta %", Order = 42, GroupName = "04. TIER A PROFILE")]
        public double S3_MaxNormalizedDeltaPct { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "31. Use Min Opp Stack", Order = 43, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseMinOppStack { get; set; }

        [NinjaScriptProperty]
        [Range(0, 20)]
        [Display(Name = "32. Min Opp Stack", Order = 44, GroupName = "04. TIER A PROFILE")]
        public int S3_MinOppStack { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "33. Use Max Opp Stack", Order = 45, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseMaxOppStack { get; set; }

        [NinjaScriptProperty]
        [Range(0, 20)]
        [Display(Name = "34. Max Opp Stack", Order = 46, GroupName = "04. TIER A PROFILE")]
        public int S3_MaxOppStack { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "35. Use Delta Divergence", Order = 47, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseDeltaDivergence { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "36. Require 3-Bar Decel", Order = 48, GroupName = "04. TIER A PROFILE")]
        public bool S3_RequireDeceleration { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "37. Use CD Slope Accel", Order = 49, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseCdSlopeAccel { get; set; }

        [NinjaScriptProperty]
        [Range(-100.0, 100.0)]
        [Display(Name = "38. Min CD Slope Accel", Order = 50, GroupName = "04. TIER A PROFILE")]
        public double S3_MinCdSlopeAccel { get; set; }

        [NinjaScriptProperty]
        [Range(1, 10)]
        [Display(Name = "39. CD Slope Accel Shift", Order = 51, GroupName = "04. TIER A PROFILE")]
        public int S3_CdSlopeAccelShift { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "40. Use Absorption", Order = 52, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseAbsorption { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 100.0)]
        [Display(Name = "41a. Min Absorption %", Order = 53, GroupName = "04. TIER A PROFILE")]
        public double S3_MinAbsorptionPct { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "41b. Use Max Absorption %", Order = 54, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseMaxAbsorption { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 100.0)]
        [Display(Name = "41c. Max Absorption %", Order = 55, GroupName = "04. TIER A PROFILE")]
        public double S3_MaxAbsorptionPct { get; set; }

        [NinjaScriptProperty]
        [Range(1, 20)]
        [Display(Name = "42. Absorption Zone Ticks", Order = 56, GroupName = "04. TIER A PROFILE")]
        public int S3_AbsorptionZoneTicks { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 20.0)]
        [Display(Name = "43. Min Absorb Multiple", Order = 57, GroupName = "04. TIER A PROFILE")]
        public double S3_MinAbsorptionMultiple { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "44. Use POC Migration", Order = 58, GroupName = "04. TIER A PROFILE")]
        public bool S3_UsePocMigration { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "45. Require POC Reversal", Order = 59, GroupName = "04. TIER A PROFILE")]
        public bool S3_RequirePocReversal { get; set; }

        [NinjaScriptProperty]
        [Range(-50.0, 50.0)]
        [Display(Name = "46. Min POC Mig Ticks", Order = 60, GroupName = "04. TIER A PROFILE")]
        public double S3_MinPocMigrationTicks { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "47. Use Stack Recency Filter", Order = 61, GroupName = "04. TIER A PROFILE")]
        public bool S3_UseRecency { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 1.0)]
        [Display(Name = "48. Min Stack Recency", Order = 62, GroupName = "04. TIER A PROFILE")]
        public double S3_MinRecency { get; set; }

        [NinjaScriptProperty]
        [Range(0.0, 1.0)]
        [Display(Name = "49. Max Stack Recency", Order = 63, GroupName = "04. TIER A PROFILE")]
        public double S3_MaxRecency { get; set; }
        // ==============================================================================
        // 05-07: RISK, SESSIONS, DATA
        // ==============================================================================
        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "Stop Loss (Ticks)", Order = 1, GroupName = "05. GLOBAL: Risk Management")]
        public int StopLossTicks { get; set; }

        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "Take Profit (Ticks)", Order = 2, GroupName = "05. GLOBAL: Risk Management")]
        public int TakeProfitTicks { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Use Break Even", Order = 3, GroupName = "05. GLOBAL: Risk Management")]
        public bool UseBreakEven { get; set; }

        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "BE Trigger (Ticks)", Order = 4, GroupName = "05. GLOBAL: Risk Management")]
        public int BreakEvenTriggerTicks { get; set; }

        [NinjaScriptProperty]
        [Range(-100, 100)]
        [Display(Name = "BE Offset (Ticks)", Order = 5, GroupName = "05. GLOBAL: Risk Management")]
        public int BreakEvenOffsetTicks { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Use Auto Trail", Order = 6, GroupName = "05. GLOBAL: Risk Management")]
        public bool UseAutoTrail { get; set; }

        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "Trail Profit Trigger (Ticks)", Order = 7, GroupName = "05. GLOBAL: Risk Management")]
        public int AutoTrailTriggerTicks { get; set; }

        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "Trail Stop Loss (Ticks)", Order = 8, GroupName = "05. GLOBAL: Risk Management")]
        public int AutoTrailStopLossTicks { get; set; }

        [NinjaScriptProperty]
        [Range(1, int.MaxValue)]
        [Display(Name = "Trail Step Freq (Ticks)", Order = 9, GroupName = "05. GLOBAL: Risk Management")]
        public int AutoTrailFrequencyTicks { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Use Max Daily Profit", Order = 10, GroupName = "05. GLOBAL: Risk Management")]
        public bool UseMaxDailyProfit { get; set; }

        [NinjaScriptProperty]
        [Range(1.0, double.MaxValue)]
        [Display(Name = "Max Daily Profit ($)", Order = 11, GroupName = "05. GLOBAL: Risk Management")]
        public double MaxDailyProfit { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Use Shadow Daily Profit Target", Order = 12, GroupName = "05. GLOBAL: Risk Management")]
        public bool UseShadowDailyProfitTracker { get; set; }

        [NinjaScriptProperty]
        [Range(1.0, double.MaxValue)]
        [Display(Name = "Shadow Daily Profit Target ($)", Order = 13, GroupName = "05. GLOBAL: Risk Management")]
        public double ShadowDailyProfitTarget { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Use Session Filter", Order = 1, GroupName = "06. GLOBAL: Sessions")]
        public bool UseSessionFilter { get; set; }

        [NinjaScriptProperty]
        [PropertyEditor("NinjaTrader.Gui.Tools.TimeEditorKey")]
        [Display(Name = "Session 1 Start", Order = 2, GroupName = "06. GLOBAL: Sessions")]
        public DateTime SessionStart { get; set; }

        [NinjaScriptProperty]
        [PropertyEditor("NinjaTrader.Gui.Tools.TimeEditorKey")]
        [Display(Name = "Session 1 End", Order = 3, GroupName = "06. GLOBAL: Sessions")]
        public DateTime SessionEnd { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Enable Trade Logging", Order = 1, GroupName = "07. GLOBAL: Data Logging")]
        public bool UseTradeLogging { get; set; }

        // ==============================================================================
        // 08: KEY LEVEL TELEMETRY / GATE
        // ==============================================================================
        [NinjaScriptProperty]
        [Display(Name = "Use Key Level Gate", Order = 1, GroupName = "08. KEY LEVELS")]
        public bool UseKeyLevelGate { get; set; }

        [NinjaScriptProperty]
        [Range(1, 100)]
        [Display(Name = "Key Level Proximity (Ticks)", Order = 2, GroupName = "08. KEY LEVELS")]
        public int KeyLevelProximityTicks { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow VWAP", Order = 3, GroupName = "08. KEY LEVELS")]
        public bool KL_AllowVWAP { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Prior Day High", Order = 4, GroupName = "08. KEY LEVELS")]
        public bool KL_AllowPDH { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Prior Day Low", Order = 5, GroupName = "08. KEY LEVELS")]
        public bool KL_AllowPDL { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Initial Balance High", Order = 6, GroupName = "08. KEY LEVELS")]
        public bool KL_AllowIBH { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Initial Balance Low", Order = 7, GroupName = "08. KEY LEVELS")]
        public bool KL_AllowIBL { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Premarket High", Order = 8, GroupName = "08. KEY LEVELS")]
        public bool KL_AllowPMH { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow Premarket Low", Order = 9, GroupName = "08. KEY LEVELS")]
        public bool KL_AllowPML { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Allow POC", Order = 10, GroupName = "08. KEY LEVELS")]
        public bool KL_AllowPOC { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Require Delta Agreement", Order = 11, GroupName = "08. KEY LEVELS")]
        public bool KL_RequireDeltaAgreement { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Require Absorption For Reversal", Order = 12, GroupName = "08. KEY LEVELS")]
        public bool KL_RequireAbsorptionForReversal { get; set; }

        [NinjaScriptProperty]
        [Display(Name = "Avoid Midday Chop", Order = 13, GroupName = "08. KEY LEVELS")]
        public bool KL_AvoidMiddayChop { get; set; }

        [NinjaScriptProperty]
        [PropertyEditor("NinjaTrader.Gui.Tools.TimeEditorKey")]
        [Display(Name = "Midday Start", Order = 14, GroupName = "08. KEY LEVELS")]
        public DateTime KL_MiddayStart { get; set; }

        [NinjaScriptProperty]
        [PropertyEditor("NinjaTrader.Gui.Tools.TimeEditorKey")]
        [Display(Name = "Midday End", Order = 15, GroupName = "08. KEY LEVELS")]
        public DateTime KL_MiddayEnd { get; set; }

        #endregion
    }
}