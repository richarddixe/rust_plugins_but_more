/*
*  <----- End-User License Agreement ----->
*  
*  You may not copy, modify, merge, publish, distribute, sublicense, or sell copies of This Software without the Developer’s consent
*  
*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, 
*  THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS 
*  BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE 
*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT 
*  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*
*  Developer: nivex (mswenson82@yahoo.com)
*
*  Copyright © 2020-2022 nivex
*/

#pragma warning disable
using Facepunch;
using Facepunch.Math;
using Network;
using Newtonsoft.Json;
using Newtonsoft.Json.Serialization;
using Oxide.Core;
using Oxide.Core.Configuration;
using Oxide.Core.Libraries.Covalence;
using Oxide.Core.Plugins;
using Oxide.Game.Rust;
using Oxide.Game.Rust.Cui;
using Oxide.Game.Rust.Libraries;
using Oxide.Plugins.RaidableBasesExtensionMethods;
using Rust;
using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Text;
using System.Text.RegularExpressions;
using UnityEngine;
using UnityEngine.AI;
using UnityEngine.SceneManagement;

namespace Oxide.Plugins
{
    [Info("Raidable Bases", "nivex", "2.7.3")]
    [Description("Create fully automated raidable bases with npcs.")]
    class RaidableBases : RustPlugin
    {
        [PluginReference]
        private Plugin
            DangerousTreasures, ZoneManager, IQEconomic, Economics, ServerRewards, GUIAnnouncements, AdvancedAlerts, Archery, Space,
            Friends, Clans, Kits, TruePVE, NightLantern, Wizardry, NextGenPVE, Imperium, Backpacks, BaseRepair, Notify, SkillTree;

        private new const string Name = "RaidableBases";
        private const int targetMask = Layers.Mask.World | Layers.Mask.Terrain | Layers.Mask.Default;
        private const int visibleMask = Layers.Mask.Deployed | Layers.Mask.Construction | targetMask;
        private const int targetMask2 = Layers.Mask.Construction | Layers.Mask.Water | targetMask;
        private const int manualMask = Layers.Mask.Deployed | Layers.Mask.Tree | targetMask2;
        private const int blockLayers = Layers.Mask.Construction | Layers.Mask.Deployed | Layers.Mask.Player_Server;
        private const int queueLayers = blockLayers | Layers.Mask.Ragdoll;

        private bool UndoStructures, UndoDeployables, UndoMounts;
        private static RaidableBases Instance { get; set; }
        private AutomatedController Automated { get; set; }
        private QueueController Queues { get; set; }
        private Coroutine setupCopyPasteObstructionRadius { get; set; }
        private float OceanLevel { get; set; }
        private RotationCycle Cycle { get; set; } = new RotationCycle();
        public List<RaidableBase> Raids { get; } = new List<RaidableBase>();
        public Dictionary<ulong, DelaySettings> PvpDelay { get; } = new Dictionary<ulong, DelaySettings>();
        public Dictionary<ulong, HumanoidBrain> HumanoidBrains { get; set; } = new Dictionary<ulong, HumanoidBrain>();
        private Dictionary<string, SkinInfo> Skins { get; } = new Dictionary<string, SkinInfo>();
        private Dictionary<NetworkableId, BMGELEVATOR> _elevators { get; set; } = new Dictionary<NetworkableId, BMGELEVATOR>();
        public static StoredData data { get; set; } = new StoredData();
        public TemporaryData temporaryData { get; set; } = new TemporaryData();
        private static StringBuilder _sb { get; set; }
        private static StringBuilder _sb2 { get; set; }
        private bool wiped { get; set; }
        private float lastSpawnRequestTime { get; set; }
        private bool IsUnloading { get; set; }
        private bool IsShuttingDown { get; set; }
        private bool bypassRestarting { get; set; }
        private BuildingTables Buildings { get; set; }
        private bool DebugMode { get; set; }
        private int despawnLimit { get; set; } = 10;
        private Dictionary<string, ItemDefinition> _deployables { get; set; } = new Dictionary<string, ItemDefinition>();
        private Dictionary<ItemDefinition, string> _definitions { get; set; } = new Dictionary<ItemDefinition, string>();
        public List<LootItem> BaseLootList { get; set; } = new List<LootItem>();
        private List<uint> ExcludedMounts { get; set; } = new List<uint> { 3552983236, 4218596772, 1845856065, 1992774774, 629849447, 4267988016, 1418740895, 2493676858, 3814928951, 1980628900, 703403829, 3061223907, 113644298, 3691382632, 3858860623, 286221745, 2230162530, 51176708, 3363531184, 3224878175 };
        private List<string> Blocks { get; set; } = new List<string> { "wall.doorway", "wall", "wall.frame", "wall.half", "wall.low", "wall.window", "foundation.triangle", "foundation", "wall.external.high.wood", "wall.external.high.stone", "wall.external.high.ice", "floor.triangle.frame", "floor.triangle", "floor.frame" };
        private List<string> TrueDamage { get; set; } = new List<string> { "spikes.floor", "barricade.metal", "barricade.woodwire", "barricade.wood", "wall.external.high.wood", "wall.external.high.stone", "wall.external.high.ice" };
        private List<string> arguments { get; set; } = new List<string> { "add", "remove", "list", "clean", "maintained", "scheduled", "toggle", "stability" };
        private List<string> unityEngineScripts { get; set; } = new List<string> { "saddletest", "fuel_storage" };
        private SkinSettingsImportedWorkshop ImportedWorkshopSkins { get; set; }
        private List<string> _lockoutKeys = new List<string>();
        private const float M_RADIUS = 25f;
        private const float CELL_SIZE = M_RADIUS / 2f;
        private List<Coroutine> loadCoroutines = new List<Coroutine>();
        private Dictionary<string, PasteData> _pasteData = new Dictionary<string, PasteData>();
        private readonly IPlayer _consolePlayer = new Game.Rust.Libraries.Covalence.RustConsolePlayer();
        private List<BaseEntity.Slot> _checkSlots = new List<BaseEntity.Slot> { BaseEntity.Slot.Lock, BaseEntity.Slot.UpperModifier, BaseEntity.Slot.MiddleModifier, BaseEntity.Slot.LowerModifier };

        public class PasteData
        {
            public bool valid;
            public float radius;
            public List<Vector3> foundations;
            public PasteData() { }
            public static PasteData Get(string baseName)
            {
                PasteData pasteData;
                if (!Instance._pasteData.TryGetValue(baseName, out pasteData))
                {
                    Instance._pasteData[baseName] = pasteData = new PasteData();
                }
                return pasteData;
            }
        }

        public enum RaidableType { None, Manual, Scheduled, Maintained, Grid }

        public enum RaidableMode { Disabled = -1, Normal = 512, Random = 9999 }

        public enum AlliedType { All, Clan, Friend, Team }

        public enum CacheType { Close, Delete, Generic, Temporary, Privilege, Submerged }

        public enum ConstructionType { Barricade, Ladder, Any }

        public class TemporaryData
        {
            [JsonIgnore]
            public Coroutine co;
            public HashSet<ulong> NID { get; set; } = new HashSet<ulong>();
            public TemporaryData() { }
            public void StartCoroutine(List<ulong> tmp)
            {
                co = ServerMgr.Instance.StartCoroutine(Purge(tmp));
            }
            public void StopCoroutine()
            {
                if (co != null)
                {
                    ServerMgr.Instance.StopCoroutine(co);
                }
            }
            public IEnumerator Purge(List<ulong> tmp)
            {
                var instruction = CoroutineEx.waitForSeconds(0.025f);
                var checks = 0;
                while (tmp.Count > 0)
                {
                    if (++checks % 25 == 0)
                    {
                        yield return instruction;
                    }
                    var uid = tmp[0];
                    NID.Remove(uid);
                    tmp.Remove(uid);
                    BaseNetworkable.serverEntities.Find(new NetworkableId(uid)).SafelyKill();
                }
                co = null;
            }
        }

        public class StoredData
        {
            public Dictionary<string, PlayerInfo> Players { get; set; } = new Dictionary<string, PlayerInfo>();
            public string RaidTime { get; set; } = DateTime.MinValue.ToString();
            public int TotalEvents { get; set; }
            public StoredData() { }
        }

        public class SpawnComparer : IComparer<RaidableSpawnLocation>
        {
            private Vector3 a;

            public SpawnComparer(Vector3 a)
            {
                this.a = a;
            }

            int IComparer<RaidableSpawnLocation>.Compare(RaidableSpawnLocation x, RaidableSpawnLocation y)
            {
                return (x.Location - a).sqrMagnitude.CompareTo((y.Location - a).sqrMagnitude);
            }
        }

        public class RandomBase
        {
            public ulong userid;
            public IPlayer user;
            public BasePlayer owner;
            public PasteData pasteData;
            public string BaseName;
            public Vector3 Position;
            public BaseProfile Profile;
            public RaidableType type;
            public RaidableSpawns spawns;
            public float Radius;
            public float heightAdj;
            public float typeDistance;
            public float protectionRadius;
            public float safeRadius;
            public float buildRadius;
            public int attempts;
            public bool autoHeight;
            public bool stability;
            public bool checkTerrain;
            public bool IsUnloading;

            public RandomBase() { }

            public RandomBase(string BaseName, BaseProfile Profile, Vector3 Position, RaidableType Type, RaidableSpawns spawns)
            {
                this.BaseName = BaseName;
                this.Position = Position;
                this.Profile = Profile;
                this.type = Type;
                this.spawns = spawns;
                this.Radius = Profile.Options.ProtectionRadius(Type);
            }

            public BuildingOptions options => Profile.Options;
            public bool hasSpawns => spawns.Spawns.Count > 0;
        }

        public class BackpackData
        {
            public DroppedItemContainer backpack;
            public BasePlayer _player;
            public ulong userID;
            public BasePlayer player => _player ?? (_player = RustCore.FindPlayerById(userID));
        }

        public class DelaySettings
        {
            public RaidableBase RaidableBase;
            public Timer Timer;
            public bool AllowPVP;
            public float time;
            public static bool CanRemoveOwner(DroppedItemContainer backpack)
            {
                DelaySettings ds;
                if (!Instance.PvpDelay.TryGetValue(backpack.playerSteamID, out ds)) return false;
                return ds.AllowPVP && config.Settings.Management.BackpacksPVP || !ds.AllowPVP && config.Settings.Management.BackpacksPVE;
            }
        }

        public class MountInfo
        {
            public Vector3 position;
            public float radius;
            public BaseMountable mountable;
        }

        public class RaidEntity
        {
            public RaidableBase raid;
            public BaseEntity entity;
            public RaidEntity(RaidableBase raid, BaseEntity entity)
            {
                this.raid = raid;
                this.entity = entity;
            }
        }

        public class SkinInfo
        {
            public List<ulong> skins = new List<ulong>();
            public List<ulong> workshopSkins = new List<ulong>();
            public List<ulong> importedSkins = new List<ulong>();
            public List<ulong> allSkins = new List<ulong>();
        }

        public class LandLevel
        {
            public float Min;
            public float Max;
        }

        public class RaidableSpawnLocation
        {
            public List<Vector3> Surroundings = new List<Vector3>();
            public Vector3 Location = Vector3.zero;
            public float WaterHeight;
            public float TerrainHeight;
            public float SpawnHeight;
            public float Radius;
            public bool AutoHeight;

            public RaidableSpawnLocation(Vector3 Location)
            {
                this.Location = Location;
            }
        }

        public class ZoneInfo
        {
            internal Vector3 Position;
            internal Vector3 Size;
            internal Vector3 extents;
            internal Matrix4x4 m;
            internal float Distance;
            internal bool isBlocked;

            public ZoneInfo(object location, object radius, object size, bool isBlocked)
            {
                var dist = Mathf.Max(config.Settings.ZoneDistance, 100f);

                this.isBlocked = isBlocked;

                Position = (Vector3)location;

                if (radius is float)
                {
                    Distance = (float)radius + M_RADIUS + dist;
                }

                if (size is Vector3 && !size.Equals(Vector3.zero))
                {
                    Size = (Vector3)size + new Vector3(dist, Position.y + 100f, dist);
                    extents = Size * 0.5f;
                    m = Matrix4x4.TRS(Position, new Quaternion(), Vector3.one);
                }
            }

            public bool IsPositionInZone(Vector3 vector)
            {
                if (Size != Vector3.zero)
                {
                    var v = m.inverse.MultiplyPoint3x4(vector);

                    return v.x <= extents.x && v.x > -extents.x && v.y <= extents.y && v.y > -extents.y && v.z <= extents.z && v.z > -extents.z;
                }
                return InRange2D(Position, vector, Distance);
            }
        }

        public class BaseProfile
        {
            public BuildingOptions Options { get; set; } = new BuildingOptions();
            public string ProfileName { get; set; }

            public BaseProfile()
            {
                Options.AdditionalBases = new Dictionary<string, List<PasteOption>>();
            }

            public BaseProfile(BuildingOptions options, string name)
            {
                Options = options;
                ProfileName = name;
            }

            public static BaseProfile Clone(BaseProfile profile)
            {
                return profile.MemberwiseClone() as BaseProfile;
            }
        }

        private class BuildingTables
        {
            public Dictionary<RaidableMode, List<LootItem>> DifficultyLootLists { get; set; } = new Dictionary<RaidableMode, List<LootItem>>();
            public Dictionary<DayOfWeek, List<LootItem>> WeekdayLootLists { get; set; } = new Dictionary<DayOfWeek, List<LootItem>>();
            public Dictionary<string, BaseProfile> Profiles { get; set; } = new Dictionary<string, BaseProfile>();
            public bool IsConfigured(string baseName) => Profiles.Exists(m => m.Key == baseName || m.Value.Options.AdditionalBases.ContainsKey(baseName));
            public List<string> Removed = new List<string>();

            public void Remove(string baseName)
            {
                if (!Profiles.Remove(baseName))
                {
                    foreach (var profile in Profiles.Values)
                    {
                        if (profile.Options.AdditionalBases.Remove(baseName))
                        {
                            Removed.Add(baseName);
                            break;
                        }
                    }
                }
                else Removed.Add(baseName);
            }
        }

        public GridControllerManager GridController { get; set; } = new GridControllerManager();

        public class GridControllerManager
        {
            internal Dictionary<RaidableType, RaidableSpawns> Spawns { get; set; } = new Dictionary<RaidableType, RaidableSpawns>();
            internal Coroutine gridCoroutine { get; set; }
            internal Coroutine fileCoroutine { get; set; }
            internal float gridTime { get; set; }

            public double GetRaidTime() => DateTime.Parse(data.RaidTime).Subtract(DateTime.Now).TotalSeconds;

            public void StartAutomation()
            {
                if (Instance.Automated.IsScheduledEnabled)
                {
                    if (data.RaidTime != DateTime.MinValue.ToString() && GetRaidTime() > config.Settings.Schedule.IntervalMax)
                    {
                        data.RaidTime = DateTime.MinValue.ToString();
                    }

                    Instance.Automated.StartCoroutine(RaidableType.Scheduled);
                }

                if (Instance.Automated.IsMaintainedEnabled)
                {
                    Instance.Automated.StartCoroutine(RaidableType.Maintained);
                }
            }

            private IEnumerator LoadFiles()
            {
                yield return Instance.LoadTables();
                yield return Instance.LoadProfiles();
                yield return CoroutineEx.waitForSeconds(5f);
                RaidableBase.IsSpawnerBusy = false;
                StartAutomation();
            }

            public void Setup()
            {
                if (Spawns.Count >= 5)
                {
                    fileCoroutine = ServerMgr.Instance.StartCoroutine(LoadFiles());
                    return;
                }

                StopCoroutine();
                gridCoroutine = ServerMgr.Instance.StartCoroutine(GenerateGrid());
            }

            public void StopCoroutine()
            {
                if (gridCoroutine != null)
                {
                    ServerMgr.Instance.StopCoroutine(gridCoroutine);
                    gridCoroutine = null;
                }
                if (fileCoroutine != null)
                {
                    ServerMgr.Instance.StopCoroutine(fileCoroutine);
                    fileCoroutine = null;
                }
            }

            private IEnumerator GenerateGrid() // Credits to Jake_Rich for helping me with this!
            {
                yield return CoroutineEx.waitForSeconds(0.1f);

                while (Performance.report.frameRate < 15 && ConVar.FPS.limit > 15)
                {
                    yield return CoroutineEx.waitForSeconds(1f);
                }

                var gridStopwatch = Stopwatch.StartNew();

                RaidableSpawns spawns = Spawns[RaidableType.Grid] = new RaidableSpawns();

                gridTime = Time.realtimeSinceStartup;

                yield return Instance.LoadTables();
                yield return Instance.LoadProfiles();
                yield return SpawnsController.SetupMonuments();

                int minPos = (int)(World.Size / -2f);
                int maxPos = (int)(World.Size / 2f);
                float maxProtectionRadius = -10000f;
                float minProtectionRadius = 10000f;
                float maxWaterDepth = 0f;
                float landLevel = 0.5f;
                int checks = 0;

                foreach (var profile in Instance.Buildings.Profiles.Values)
                {
                    maxProtectionRadius = Mathf.Max(profile.Options.ProtectionRadii.Max(), maxProtectionRadius);

                    minProtectionRadius = Mathf.Min(profile.Options.ProtectionRadii.Min(), minProtectionRadius);

                    maxWaterDepth = Mathf.Max(maxWaterDepth, profile.Options.Water.WaterDepth);

                    landLevel = Mathf.Max(Mathf.Clamp(profile.Options.LandLevel, 0.5f, 3f), landLevel);
                }

                if (!config.Settings.Management.AllowOnBeach && !config.Settings.Management.AllowInland)
                {
                    Puts("Grid has failed initialization. Your configuration does not have any spawn options for beaches or inland enabled!");
                    gridCoroutine = null;
                    gridStopwatch.Stop();
                    yield break;
                }

                var blockedPositions = config.Settings.Management.BlockedPositions.ToList();
                var zero = blockedPositions.Find(x => x.position == Vector3.zero);

                if (zero == null)
                {
                    blockedPositions.Add(zero = new ManagementSettingsLocations(Vector3.zero, 200f));
                }

                if (zero.radius < 200f)
                {
                    zero.radius = 200f;
                }

                var wtObj = Convert.ToSingle(Interface.Oxide.CallHook("GetGridWaitTime"));
                var waitTime = CoroutineEx.waitForSeconds(wtObj > 0f ? wtObj : 0.0035f);
                var prefabs = config.Settings.Management.BlockedPrefabs.ToDictionary(kvp => kvp.Key, kvp => kvp.Value);
                var blockedMapPrefabs = Pool.Get<Dictionary<Vector3, float>>();

                prefabs.Remove("test_prefab");
                prefabs.Remove("test_prefab_2");

                if (prefabs.Count > 0)
                {
                    foreach (var prefab in World.Serialization.world.prefabs)
                    {
                        string fullname;
                        if (!StringPool.toString.TryGetValue(prefab.id, out fullname))
                        {
                            continue;
                        }
                        string shortprefabname = Oxide.Core.Utility.GetFileNameWithoutExtension(fullname);
                        float dist;
                        if (prefabs.TryGetValue(shortprefabname, out dist))
                        {
                            var vector = new Vector3(prefab.position.x, prefab.position.y, prefab.position.z);
                            blockedMapPrefabs[vector] = dist;
                        }
                    }
                }

                bool hasBlockedMapPrefabs = blockedMapPrefabs.Count > 0;
                bool hasBlockedPositions = blockedPositions.Count > 0;

                for (float x = minPos; x < maxPos; x += CELL_SIZE)
                {
                    for (float z = minPos; z < maxPos; z += CELL_SIZE)
                    {
                        var position = new Vector3(x, 0f, z);

                        if (hasBlockedPositions && blockedPositions.Exists(a => InRange2D(position, a.position, a.radius)))
                        {
                            continue;
                        }

                        if (hasBlockedMapPrefabs && SpawnsController.IsBlockedByMapPrefab(blockedMapPrefabs, position))
                        {
                            continue;
                        }

                        position.y = SpawnsController.GetSpawnHeight(position);

                        SpawnsController.ExtractLocation(spawns, position, landLevel, minProtectionRadius, maxProtectionRadius, maxWaterDepth);

                        if (++checks >= 25)
                        {
                            checks = 0;
                            yield return waitTime;
                        }
                    }
                }

                blockedMapPrefabs.Clear();
                Pool.Free(ref blockedMapPrefabs);
                RaidableBase.IsSpawnerBusy = false;
                Instance.GridController.StartAutomation();
                Instance.Queues.Messages.Clear();
                gridStopwatch.Stop();
                gridCoroutine = null;

                Puts(mx("Initialized Grid", null, Math.Floor(gridStopwatch.Elapsed.TotalSeconds), gridStopwatch.Elapsed.Milliseconds, World.Size, spawns.Spawns.Count));
            }

            public void LoadSpawns()
            {
                Spawns = new Dictionary<RaidableType, RaidableSpawns>();
                Spawns.Add(RaidableType.Grid, new RaidableSpawns());

                if (SpawnsFileValid(config.Settings.Manual.SpawnsFile))
                {
                    var spawns = GetSpawnsLocations(config.Settings.Manual.SpawnsFile);

                    if (spawns?.Count > 0)
                    {
                        Puts(mx("LoadedManual", null, spawns.Count));
                        Spawns[RaidableType.Manual] = new RaidableSpawns(spawns);
                    }
                }

                if (SpawnsFileValid(config.Settings.Schedule.SpawnsFile))
                {
                    var spawns = GetSpawnsLocations(config.Settings.Schedule.SpawnsFile);

                    if (spawns?.Count > 0)
                    {
                        Puts(mx("LoadedScheduled", null, spawns.Count));
                        Spawns[RaidableType.Scheduled] = new RaidableSpawns(spawns);
                    }
                }

                if (SpawnsFileValid(config.Settings.Maintained.SpawnsFile))
                {
                    var spawns = GetSpawnsLocations(config.Settings.Maintained.SpawnsFile);

                    if (spawns?.Count > 0)
                    {
                        Puts(mx("LoadedMaintained", null, spawns.Count));
                        Spawns[RaidableType.Maintained] = new RaidableSpawns(spawns);
                    }
                }
            }

            public bool SpawnsFileValid(string spawnsFile)
            {
                if (string.IsNullOrEmpty(spawnsFile) || spawnsFile.Equals("none", StringComparison.OrdinalIgnoreCase))
                {
                    return false;
                }

                return FileExists($"SpawnsDatabase{Path.DirectorySeparatorChar}{spawnsFile}");
            }

            public HashSet<RaidableSpawnLocation> GetSpawnsLocations(string spawnsFile)
            {
                Spawnfile data;
                var locations = new HashSet<RaidableSpawnLocation>();

                try
                {
                    data = Interface.Oxide.DataFileSystem.ReadObject<Spawnfile>($"SpawnsDatabase{Path.DirectorySeparatorChar}{spawnsFile}");
                }
                catch (JsonReaderException)
                {
                    return locations;
                }

                if (data == null)
                {
                    return locations;
                }

                foreach (var element in data.spawnPoints)
                {
                    if (element.Value == null) continue;

                    var value = element.Value.ToString();

                    if (string.IsNullOrEmpty(value)) continue;

                    var vector = value.ToVector3();

                    if (vector == Vector3.zero) continue;

                    locations.Add(new RaidableSpawnLocation(vector));
                }

                return locations;
            }
        }

        private class Spawnfile
        {
            public Dictionary<string, object> spawnPoints = new Dictionary<string, object>();
        }

        public class QueueController
        {
            internal Queue<RandomBase> queue = new Queue<RandomBase>();
            internal DebugMessages Messages = new DebugMessages();
            internal Coroutine _coroutine;
            internal int spawnChecks;
            internal bool Paused;

            internal bool Any => queue.Count > 0;

            public class DebugMessages
            {
                public class Info
                {
                    public int amount = 1;
                    public List<string> values = new List<string>();
                    public override string ToString()
                    {
                        if (values.Count > 0)
                        {
                            return $": {string.Join(", ", values.ToArray())}";
                        }
                        return string.Empty;
                    }
                }

                internal Dictionary<string, Info> _elements = new Dictionary<string, Info>();
                internal IPlayer DebugUser;

                public string Add(string element, object obj = null)
                {
                    if (string.IsNullOrEmpty(element))
                    {
                        return null;
                    }
                    Info info;
                    if (!_elements.TryGetValue(element, out info))
                    {
                        if (_elements.Count >= 20)
                        {
                            _elements.Remove(_elements.ElementAt(0).Key);
                        }
                        _elements[element] = info = new Info();
                    }
                    else info.amount++;
                    if (obj == null)
                    {
                        return element;
                    }
                    string value = obj.ToString().Replace("(", "").Replace(")", "").Replace(",", "");
                    if (!info.values.Contains(value))
                    {
                        if (info.values.Count >= 5)
                        {
                            info.values.RemoveAt(0);
                        }
                        info.values.Add(value);
                    }
                    return $"{element}: {value}";
                }
                public void Clear()
                {
                    _elements.Clear();
                }
                public bool Any()
                {
                    return _elements.Count > 0;
                }
                public void PrintAll(IPlayer user = null)
                {
                    if (_elements.Count > 0 && IsInstanceValid && Instance.DebugMode)
                    {
                        foreach (var element in _elements)
                        {
                            PrintInternal(user, $"{element.Value.amount}x - {element.Key}{element.Value.ToString()}");
                        }
                        Clear();
                    }
                }
                private bool PrintInternal(IPlayer user, string message)
                {
                    if (!string.IsNullOrEmpty(message) && IsInstanceValid && Instance.DebugMode)
                    {
                        if (user == null)
                        {
                            Puts("DEBUG: {0}", message);
                        }
                        else user.Reply($"DEBUG: {message}");
                        return true;
                    }
                    return false;
                }
                public void Log(string baseName, string message)
                {
                    Instance?.Buildings?.Remove(baseName);
                    RaidableBase.IsSpawnerBusy = false;
                    Print(message);
                    Puts(message);
                }
                public bool Print(string message)
                {
                    Print(DebugUser, message, null);
                    return false;
                }
                public void Print(string message, object obj)
                {
                    Print(DebugUser, message, obj);
                }
                public void Print(IPlayer user, string message, object obj)
                {
                    if (!PrintInternal(user, obj == null ? message : $"{message}: {obj}"))
                    {
                        Add(message, obj);
                    }
                }
                public void PrintLast(string id = null)
                {
                    if (_elements.Count > 0 && IsInstanceValid && Instance.DebugMode)
                    {
                        PrintInternal(DebugUser, GetLast(id));
                    }
                }
                public string GetLast(string id = null)
                {
                    if (_elements.Count == 0)
                    {
                        return m("CannotFindPosition", id);
                    }
                    var element = _elements.ElementAt(_elements.Count - 1);
                    _elements.Remove(element.Key);
                    return $"{element.Value.amount}x - {element.Key}{element.Value.ToString()}";
                }
            }

            public QueueController()
            {
                spawnChecks = Mathf.Clamp(config.Settings.Management.SpawnChecks, 1, 500);
            }

            public void StartCoroutine()
            {
                StopCoroutine();
                _coroutine = ServerMgr.Instance.StartCoroutine(FindEventPosition());
            }

            public void StopCoroutine()
            {
                if (_coroutine != null)
                {
                    ServerMgr.Instance.StopCoroutine(_coroutine);
                    _coroutine = null;
                }

                queue.ToList().ForEach(sp =>
                {
                    sp.IsUnloading = true;
                });

                queue.Clear();
            }

            public void Add(RandomBase sp)
            {
                if (!queue.Contains(sp))
                {
                    queue.Enqueue(sp);
                }
            }

            private void Spawn(RandomBase rb, Vector3 position)
            {
                if (!rb.IsUnloading && IsInstanceValid)
                {
                    rb.Position = position;

                    if (Instance.PasteBuilding(rb))
                    {
                        RaidableBase.IsSpawnerBusy = true;

                        Teleport(rb);
                    }
                }
            }

            private void Teleport(RandomBase rb)
            {
                if (rb.user != null && rb.user.IsAdmin && rb.user.IsConnected)
                {
                    rb.user.Teleport(rb.Position.x, rb.Position.y, rb.Position.z);
                }
            }

            private bool CanBypassPause(RandomBase rb)
            {
                if (rb.type == RaidableType.Manual)
                {
                    return rb.user != null;
                }
                return false;
            }

            private IEnumerator FindEventPosition()
            {
                CacheType cacheType;
                int checks = 0;
                RandomBase spq;
                string topology = "";

                while (true)
                {
                    if (++checks >= spawnChecks)
                    {
                        yield return CoroutineEx.waitForSeconds(0.025f);
                        checks = 0;
                        continue;
                    }

                    if (!queue.TryPeek(out spq))
                    {
                        yield return CoroutineEx.waitForSeconds(1f);
                        continue;
                    }

                    if (Instance.Buildings.Removed.Contains(spq.BaseName))
                    {
                        queue.Dequeue();
                        continue;
                    }

                    if (!spq.IsUnloading && spq.Position != Vector3.zero)
                    {
                        Spawn(spq, spq.Position);
                        yield return CoroutineEx.waitForSeconds(1f);
                        queue.Dequeue();
                        continue;
                    }

                    spq.spawns.Check();

                    while (spq.hasSpawns)
                    {
                        if (!IsInstanceValid || spq.IsUnloading)
                        {
                            _coroutine = null;
                            yield break;
                        }

                        if (++checks >= spawnChecks)
                        {
                            checks = 0;
                            yield return CoroutineEx.waitForSeconds(0.025f);
                        }

                        if (RaidableBase.IsSpawnerBusy || Paused && !CanBypassPause(spq))
                        {
                            yield return CoroutineEx.waitForSeconds(1f);
                            continue;
                        }

                        spq.attempts++;

                        var rsl = spq.spawns.GetRandom(spq.options.Water);
                        var vector = rsl.Location;

                        if (!TopologyChecks(spq, vector, topology))
                        {
                            continue;
                        }

                        vector.y = GetAdjustedHeight(spq, vector);

                        if (IsTooClose(spq, vector))
                        {
                            continue;
                        }

                        if (IsAreaManuallyBlocked(spq, vector))
                        {
                            continue;
                        }

                        if (CanSpawnCustomMaintained(spq, vector))
                        {
                            yield return CoroutineEx.waitForSeconds(1f);
                            break;
                        }

                        if (CanSpawnCustomSchedule(spq, vector))
                        {
                            yield return CoroutineEx.waitForSeconds(1f);
                            break;
                        }

                        if (IsSubmerged(spq, rsl, vector))
                        {
                            continue;
                        }

                        if (!IsAreaSafe(spq, rsl, vector, out cacheType))
                        {
                            continue;
                        }

                        if (!spq.pasteData.valid)
                        {
                            yield return SetupCopyPasteRadius(spq);
                        }

                        if (IsObstructed(spq, vector))
                        {
                            continue;
                        }

                        Messages.Add("Spawn location found", vector);
                        Spawn(spq, vector);
                        yield return CoroutineEx.waitForSeconds(1f);
                        break;
                    }

                    queue.Dequeue();
                    CheckSpawner(spq);
                }

                _coroutine = null;
            }

            private void CheckSpawner(RandomBase spq)
            {
                if (!RaidableBase.IsSpawnerBusy)
                {
                    if (spq.type == RaidableType.Manual)
                    {
                        if (spq.user == null)
                        {
                            Puts(mx("CannotFindPosition"));
                        }
                        else spq.user.Reply(m("CannotFindPosition", spq.user.Id));
                    }

                    spq.spawns.TryAddRange();
                    Messages.PrintAll();
                }
            }

            private bool IsObstructed(RandomBase spq, Vector3 vector)
            {
                if (!spq.spawns.IsCustomSpawn && SpawnsController.IsObstructed(vector, spq.pasteData.radius, Mathf.Clamp(spq.options.LandLevel, -3f, 3f), spq.options.Setup.ForcedHeight))
                {
                    Messages.Add("Area is obstructed", vector);
                    spq.spawns.RemoveNear(vector, spq.protectionRadius / 2f, CacheType.Temporary, spq.type);
                    return true;
                }
                return false;
            }

            private IEnumerator SetupCopyPasteRadius(RandomBase spq)
            {
                yield return Instance.SetupCopyPasteObstructionRadius(spq.BaseName, spq.options.ProtectionRadii.Obstruction == -1 ? 0f : GetObstructionRadius(spq.options.ProtectionRadii, RaidableType.None));
            }

            private bool IsAreaSafe(RandomBase spq, RaidableSpawnLocation rsl, Vector3 vector, out CacheType cacheType)
            {
                if (!SpawnsController.IsAreaSafe(vector, spq.safeRadius, spq.buildRadius, queueLayers, out cacheType, spq.type))
                {
                    if (cacheType == CacheType.Delete)
                    {
                        spq.spawns.Remove(rsl, cacheType);
                    }
                    else if (cacheType == CacheType.Privilege)
                    {
                        spq.spawns.RemoveNear(vector, spq.buildRadius, cacheType, spq.type);
                    }
                    else spq.spawns.RemoveNear(vector, spq.safeRadius / 2f, cacheType, spq.type);
                    return false;
                }
                return true;
            }

            private bool IsSubmerged(RandomBase spq, RaidableSpawnLocation rsl, Vector3 vector)
            {
                if (!spq.spawns.IsCustomSpawn && spq.options.Setup.ForcedHeight == -1f && SpawnsController.IsSubmerged(spq.options.Water, rsl))
                {
                    Messages.Add("Area is submerged", vector);
                    return true;
                }
                return false;
            }

            private bool CanSpawnCustomSchedule(RandomBase spq, Vector3 vector)
            {
                if (spq.type == RaidableType.Scheduled && spq.spawns.IsCustomSpawn && (config.Settings.Schedule.Ignore || config.Settings.Schedule.SafeRadius > 0f))
                {
                    if (config.Settings.Schedule.SafeRadius <= 0f)
                    {
                        Messages.Add("Ignoring safe checks and spawning Scheduled base", vector);
                        Spawn(spq, vector);
                        return true;
                    }
                    else spq.safeRadius = config.Settings.Schedule.SafeRadius;
                }
                return false;
            }

            private bool CanSpawnCustomMaintained(RandomBase spq, Vector3 vector)
            {
                if (spq.type == RaidableType.Maintained && spq.spawns.IsCustomSpawn && (config.Settings.Maintained.Ignore || config.Settings.Maintained.SafeRadius > 0f))
                {
                    if (config.Settings.Maintained.SafeRadius <= 0f)
                    {
                        Messages.Add("Ignoring safe checks and spawning Maintained base", vector);
                        Spawn(spq, vector);
                        return true;
                    }
                    else spq.safeRadius = config.Settings.Maintained.SafeRadius;
                }
                return false;
            }

            internal bool IsAreaManuallyBlocked(RandomBase spq, Vector3 vector)
            {
                if (config.Settings.Management.BlockedPositions.Exists(x => InRange2D(vector, x.position, x.radius)))
                {
                    spq.spawns.RemoveNear(vector, spq.options.ProtectionRadius(spq.type), CacheType.Close, spq.type);
                    Messages.Add("Area is manually blocked (Block Spawns At Positions)", vector);
                    return true;
                }
                return false;
            }

            private bool IsTooClose(RandomBase spq, Vector3 vector)
            {
                if (spq.typeDistance > 0 && RaidableBase.IsTooClose(vector, spq.typeDistance))
                {
                    spq.spawns.RemoveNear(vector, spq.options.ProtectionRadius(spq.type), CacheType.Close, spq.type);
                    Messages.Add("Too close to another raid base (Spawn Bases X Distance Apart)", vector);
                    return true;
                }
                return false;
            }

            private float GetAdjustedHeight(RandomBase spq, Vector3 vector)
            {
                if (spq.options.Setup.ForcedHeight != -1)
                {
                    return spq.options.Setup.ForcedHeight;
                }
                return vector.y + spq.options.Setup.PasteHeightAdjustment;
            }

            private bool TopologyChecks(RandomBase spq, Vector3 vector, string topology)
            {
                if (!spq.spawns.IsCustomSpawn && !SpawnsController.TopologyChecks(vector, spq.protectionRadius, out topology))
                {
                    spq.spawns.RemoveNear(vector, M_RADIUS, CacheType.Delete, spq.type);
                    Messages.Add($"Spawn is blocked on {topology} topology", vector);
                    return false;
                }
                return true;
            }
        }

        private static float GetObstructionRadius(BuildingOptionsProtectionRadius radii, RaidableType type)
        {
            if (radii.Obstruction > 0)
            {
                return Mathf.Clamp(radii.Obstruction, CELL_SIZE, radii.Get(type));
            }
            return radii.Get(type);
        }

        public class AutomatedController
        {
            internal Coroutine _maintainedCoroutine { get; set; }
            internal Coroutine _scheduledCoroutine { get; set; }
            internal bool IsMaintainedEnabled { get; set; }
            internal bool IsScheduledEnabled { get; set; }
            internal RaidableBases Instance { get; set; }
            internal int _maxOnce { get; set; }

            public AutomatedController(RaidableBases instance, bool a, bool b)
            {
                Instance = instance;
                IsMaintainedEnabled = a;
                IsScheduledEnabled = b;
            }

            public void StopCoroutine(RaidableType type, IPlayer user = null)
            {
                if (type == RaidableType.Scheduled && _scheduledCoroutine != null)
                {
                    if (user != null) user.Reply(mx("ReloadScheduleCo", user.Id));
                    ServerMgr.Instance.StopCoroutine(_scheduledCoroutine);
                    _scheduledCoroutine = null;
                }
                else if (type == RaidableType.Maintained && _maintainedCoroutine != null)
                {
                    if (user != null) user.Reply(mx("ReloadMaintainCo", user.Id));
                    ServerMgr.Instance.StopCoroutine(_maintainedCoroutine);
                    _maintainedCoroutine = null;
                }
            }

            public void StartCoroutine(RaidableType type, IPlayer user = null)
            {
                StopCoroutine(type, user);

                if (type == RaidableType.Scheduled ? !IsScheduledEnabled || config.Settings.Schedule.Max <= 0 : !IsMaintainedEnabled || config.Settings.Maintained.Max <= 0)
                {
                    return;
                }

                if (Instance.IsGridLoading)
                {
                    Instance.timer.Once(1f, () => StartCoroutine(type));
                    return;
                }

                if (type == RaidableType.Scheduled && data.RaidTime == DateTime.MinValue.ToString())
                {
                    ScheduleNextAutomatedEvent();
                }

                if (type == RaidableType.Scheduled)
                {
                    Instance.timer.Once(0.2f, () => _scheduledCoroutine = ServerMgr.Instance.StartCoroutine(ScheduleCoroutine()));
                }
                else Instance.timer.Once(0.2f, () => _maintainedCoroutine = ServerMgr.Instance.StartCoroutine(MaintainCoroutine()));
            }

            private IEnumerator MaintainCoroutine()
            {
                float timeBetweenSpawns = Mathf.Max(1f, config.Settings.Maintained.Time);

                while (IsInstanceValid)
                {
                    if (!CanSpawn(RaidableType.Maintained, BasePlayer.activePlayerList.Count, config.Settings.Maintained.PlayerLimit, config.Settings.Maintained.PlayerLimitMax, config.Settings.Maintained.Max, false))
                    {
                        yield return CoroutineEx.waitForSeconds(5f);
                    }
                    else if (!Instance.Queues.Any && IsInstanceValid)
                    {
                        yield return ProcessEvent(RaidableType.Maintained, timeBetweenSpawns);
                    }
                    else if (Instance.Queues.Messages.Any())
                    {
                        Instance.Queues.Messages.PrintLast();
                    }

                    yield return CoroutineEx.waitForSeconds(5f);
                }

                _maintainedCoroutine = null;
            }

            private IEnumerator ScheduleCoroutine()
            {
                float timeBetweenSpawns = Mathf.Max(1f, config.Settings.Schedule.Time);

                while (IsInstanceValid)
                {
                    if (CanSpawn(RaidableType.Scheduled, BasePlayer.activePlayerList.Count, config.Settings.Schedule.PlayerLimit, config.Settings.Schedule.PlayerLimitMax, config.Settings.Schedule.Max, true))
                    {
                        while (RaidableBase.Get(RaidableType.Scheduled) < config.Settings.Schedule.Max && MaxOnce())
                        {
                            if (SaveRestore.IsSaving)
                            {
                                Instance.Queues.Messages.Print("Scheduled: Server saving");
                                yield return CoroutineEx.waitForSeconds(15f);
                            }
                            else if (!Instance.Queues.Any && IsInstanceValid)
                            {
                                yield return ProcessEvent(RaidableType.Scheduled, timeBetweenSpawns);
                            }
                            else if (Instance.Queues.Messages.Any())
                            {
                                Instance.Queues.Messages.PrintLast();
                            }

                            yield return CoroutineEx.waitForSeconds(1f);
                        }

                        yield return CoroutineEx.waitForSeconds(ScheduleNextAutomatedEvent());
                    }

                    yield return CoroutineEx.waitForSeconds(5f);
                }

                _scheduledCoroutine = null;
            }

            private IEnumerator ProcessEvent(RaidableType type, float timeBetweenSpawns)
            {
                Instance.SpawnRandomBase(type);
                yield return CoroutineEx.waitForSeconds(1f);
                yield return new WaitWhile(() => Instance.Queues.Any);

                if (!RaidableBase.IsSpawnerBusy)
                {
                    yield break;
                }

                if (type == RaidableType.Scheduled)
                {
                    _maxOnce++;
                }

                Vector3 pastedLocation;
                Instance.Queues.Messages.Print($"{type}: Waiting for base to be setup", Instance.IsBusy(out pastedLocation) ? pastedLocation : (object)null);

                yield return new WaitWhile(() => RaidableBase.IsSpawnerBusy);

                Instance.Queues.Messages.Print($"{type}: Waiting {timeBetweenSpawns} seconds");
                yield return CoroutineEx.waitForSeconds(timeBetweenSpawns);
            }

            private float ScheduleNextAutomatedEvent()
            {
                var raidInterval = Core.Random.Range(config.Settings.Schedule.IntervalMin, config.Settings.Schedule.IntervalMax + 1);

                _maxOnce = 0;
                data.RaidTime = DateTime.Now.AddSeconds(raidInterval).ToString();
                Puts(mx("Next Automated Raid", null, FormatTime(raidInterval, null), data.RaidTime));
                Instance.Queues.Messages.Print("Scheduled next automated event");

                return (float)raidInterval;
            }

            private bool MaxOnce()
            {
                return config.Settings.Schedule.MaxOnce <= 0 || _maxOnce < config.Settings.Schedule.MaxOnce;
            }

            private bool CanSpawn(RaidableType type, int onlinePlayers, int playerLimit, int playerLimitMax, int maxEvents, bool checkRaidTime)
            {
                if (onlinePlayers < playerLimit)
                {
                    return Instance.Queues.Messages.Print($"{type}: Insufficient amount of players online {onlinePlayers}/{playerLimit}");
                }
                else if (onlinePlayers > playerLimitMax)
                {
                    return Instance.Queues.Messages.Print($"{type}: Too many players online {onlinePlayers}/{playerLimitMax}");
                }
                else if (RaidableBase.IsSpawnerBusy || Instance.Raids.Exists(raid => raid.IsDespawning || raid.IsLoading))
                {
                    return Instance.Queues.Messages.Print($"{type}: Waiting for a base to finish its task");
                }
                else if (maxEvents > 0 && RaidableBase.Get(type) >= maxEvents)
                {
                    return Instance.Queues.Messages.Print($"{type}: The max amount of events are spawned");
                }
                else if (checkRaidTime && Instance.GridController.GetRaidTime() > 0)
                {
                    return Instance.Queues.Messages.Print($"{type}: Waiting on timer for next event");
                }
                else if (SaveRestore.IsSaving)
                {
                    return Instance.Queues.Messages.Print($"{type}: Server saving");
                }

                return Instance.IsCopyPasteLoaded(null);
            }
        }

        public class BMGELEVATOR : FacepunchBehaviour // credits: bmgjet
        {
            internal const string ElevatorPanelName = "RB_UI_Elevator";

            internal Elevator _elevator;
            internal RaycastHit hit;
            internal BaseEntity hitEntity;
            internal RaidableBase raid;
            internal BuildingOptionsElevators options;
            internal Dictionary<ulong, BasePlayer> _UI = new Dictionary<ulong, BasePlayer>();
            internal bool HasButton;
            internal NetworkableId uid;
            internal int CurrentFloor;
            internal int returnDelay = 60;
            internal float Floors;
            internal float lastPermissionTime;
            internal float _LiftSpeedPerMetre = 3f;

            private void Awake()
            {
                _elevator = GetComponent<Elevator>();
                _elevator.LiftSpeedPerMetre = _LiftSpeedPerMetre;
            }

            private void OnDestroy()
            {
                _elevator.SafelyKill();
                _UI.Values.ToList().ForEach(DestroyUi);
                Instance?._elevators.Remove(uid);
                try { CancelInvoke(); } catch { }
            }

            public bool ValidPosition => !_elevator.IsKilled() && !_elevator.liftEntity.IsKilled();

            public Vector3 ServerPosition => _elevator.liftEntity.transform.position;

            private Vector3 GetWorldSpaceFloorPosition(int targetFloor)
            {
                int num = _elevator.Floor - targetFloor;
                Vector3 b = Vector3.up * ((float)num * _elevator.FloorHeight);
                b.y -= 1f;
                return base.transform.position - b;
            }

            public void GoToFloor(Elevator.Direction Direction = Elevator.Direction.Down, bool FullTravel = false, int forcedFloor = -1)
            {
                if (_elevator.HasFlag(BaseEntity.Flags.Busy))
                {
                    return;
                }
                int maxFloors = (int)(Floors / 3f);
                if (forcedFloor != -1)
                {
                    int targetFloor = Mathf.RoundToInt((forcedFloor - ServerPosition.y) / 3);
                    if (targetFloor == 0 && CurrentFloor == 0) targetFloor = maxFloors;
                    else if (targetFloor == 0 && CurrentFloor == maxFloors) targetFloor = -maxFloors;
                    CurrentFloor += targetFloor;
                    if (CurrentFloor > maxFloors) CurrentFloor = maxFloors;
                    if (CurrentFloor < 0) CurrentFloor = 0;
                }
                else
                {
                    if (Direction == Elevator.Direction.Up)
                    {
                        CurrentFloor++;
                        if (FullTravel) CurrentFloor = (int)(Floors / _elevator.FloorHeight);
                        if ((CurrentFloor * 3) > Floors) CurrentFloor = (int)(Floors / _elevator.FloorHeight);
                    }
                    else
                    {
                        if (GamePhysics.CheckSphere(ServerPosition - new Vector3(0, 1f, 0), 0.5f, Layers.Mask.Construction | Layers.Server.Deployed, QueryTriggerInteraction.Ignore))
                        {
                            _elevator.Invoke(Retry, returnDelay);
                            return;
                        }

                        CurrentFloor--;
                        if (CurrentFloor < 0 || FullTravel) CurrentFloor = 0;
                    }
                }
                Vector3 worldSpaceFloorPosition = GetWorldSpaceFloorPosition(CurrentFloor);
                if (!GamePhysics.LineOfSight(ServerPosition, worldSpaceFloorPosition, 2097152))
                {
                    if (Direction == Elevator.Direction.Up)
                    {
                        if (!Physics.Raycast(ServerPosition, Vector3.up, out hit, 21f) || (hitEntity = hit.GetEntity()).IsNull())
                        {
                            return;
                        }
                        CurrentFloor = (int)(hitEntity.transform.position.Distance(_elevator.transform.position) / 3);
                        worldSpaceFloorPosition = GetWorldSpaceFloorPosition(CurrentFloor);
                    }
                    else
                    {
                        if (!Physics.Raycast(ServerPosition - new Vector3(0, 2.9f, 0), Vector3.down, out hit, 21f) || (hitEntity = hit.GetEntity()).IsNull() || hitEntity.ShortPrefabName == "foundation" || hitEntity.ShortPrefabName == "elevator.static")
                        {
                            _elevator.Invoke(Retry, returnDelay);
                            return;
                        }
                        CurrentFloor = (int)(hitEntity.transform.position.Distance(_elevator.transform.position) / 3) + 1;
                        worldSpaceFloorPosition = GetWorldSpaceFloorPosition(CurrentFloor);
                    }
                }
                Vector3 vector = transform.InverseTransformPoint(worldSpaceFloorPosition);
                float timeToTravel = _elevator.TimeToTravelDistance(Mathf.Abs(_elevator.liftEntity.transform.localPosition.y - vector.y));
                LeanTween.moveLocalY(_elevator.liftEntity.gameObject, vector.y, timeToTravel);
                _elevator.SetFlag(BaseEntity.Flags.Busy, true, false, true);
                _elevator.liftEntity.ToggleHurtTrigger(true);
                _elevator.Invoke(_elevator.ClearBusy, timeToTravel);
                _elevator.CancelInvoke(ElevatorToGround);
                _elevator.Invoke(ElevatorToGround, timeToTravel + returnDelay);
            }

            private void Retry()
            {
                GoToFloor(Elevator.Direction.Down, true);
            }

            private void ElevatorToGround()
            {
                if (CurrentFloor != 0)
                {
                    if (_elevator.HasFlag(BaseEntity.Flags.Busy))
                    {
                        _elevator.Invoke(ElevatorToGround, 5f);
                        return;
                    }
                    GoToFloor(Elevator.Direction.Down, true);
                }
            }

            public void Init(RaidableBase raid)
            {
                this.raid = raid;
                options = raid.Options.Elevators;
                _elevator._maxHealth = options.ElevatorHealth;
                _elevator.InitializeHealth(options.ElevatorHealth, options.ElevatorHealth);

                if (options.Enabled)
                {
                    InvokeRepeating(ShowHealthUI, 10, 1);
                }

                if (HasButton)
                {
                    Instance.Subscribe(nameof(OnButtonPress));
                }
            }

            private void ShowHealthUI()
            {
                var players = raid.GetIntruders().Where(player => player.Distance(ServerPosition) <= 3f);
                foreach (var player in _UI.Values.ToList())
                {
                    if (!players.Contains(player)) // || !GamePhysics.LineOfSight(ServerPosition, player.transform.position, 2097152))
                    {
                        DestroyUi(player);
                        _UI.Remove(player.userID);
                    }
                }
                foreach (var player in players)
                {
                    if (!player.IsSleeping()) // && GamePhysics.LineOfSight(ServerPosition, player.transform.position, 2097152))
                    {
                        var translated = mx("Elevator Health", player.UserIDString);
                        var color = UI.Color(options.PanelColor, options.PanelAlpha.Value);
                        var elements = UI.CreateElementContainer(ElevatorPanelName, color, options.AnchorMin, options.AnchorMax);
                        var text = $"{translated} {_elevator._health:#.##}/{_elevator._maxHealth}";
                        UI.CreateLabel(ref elements, ElevatorPanelName, "1 1 1 1", text, 16, "0 0", "1 1");
                        DestroyUi(player);
                        CuiHelper.AddUi(player, elements);
                        _UI[player.userID] = player;
                    }
                }
            }

            public static void DestroyUi(BasePlayer player) => CuiHelper.DestroyUi(player, ElevatorPanelName);

            public static Dictionary<Elevator, BMGELEVATOR> FixElevators(RaidableBase raid)
            {
                var elevators = new List<BaseEntity>();
                var bmgs = new Dictionary<Elevator, BMGELEVATOR>();
                bool hasButton = false;

                foreach (BaseEntity entity in raid.Entities.ToList())
                {
                    if (entity is Elevator || entity is ElevatorLift)
                    {
                        elevators.Add(entity);
                        raid.Entities.Remove(entity);
                    }
                    else if (entity is PressButton)
                    {
                        hasButton = true;
                    }
                }

                foreach (var list in SplitElevators(elevators))
                {
                    BMGELEVATOR bmgELEVATOR;
                    Elevator elevator = FixElevators(list, out bmgELEVATOR);
                    if (!elevator.IsNull())
                    {
                        bmgELEVATOR.HasButton = hasButton;
                        bmgs[elevator] = bmgELEVATOR;
                        raid.AddEntity(elevator);
                    }
                }

                return bmgs;
            }

            public static Elevator FixElevators(List<BaseEntity> elevators, out BMGELEVATOR bmgELEVATOR)
            {
                bmgELEVATOR = null;
                if (elevators?.Count > 0)
                {
                    Elevator e = FixElevator(elevators, out bmgELEVATOR);
                    if (!e.IsNull())
                    {
                        elevators.Add(e);
                        return e;
                    }
                }
                return null;
            }

            private static void CleanElevatorKill(BaseEntity entity)
            {
                if (!entity.IsKilled())
                {
                    entity.transform.position = new Vector3(0, -100f, 0);
                    Instance.NextFrame(entity.SafelyKill);
                }
            }

            public static Elevator FixElevator(List<BaseEntity> elevators, out BMGELEVATOR bmgELEVATOR)
            {
                bmgELEVATOR = null;
                if (elevators.Count == 1)
                {
                    CleanElevatorKill(elevators[0]);
                    return null;
                }
                Vector3 bottom = new Vector3(999f, 999f, 999f);
                Vector3 top = new Vector3(-999f, -999f, -999f);
                Quaternion rot = elevators[0].transform.rotation;
                foreach (BaseEntity entity in elevators)
                {
                    if (entity.transform.position.y < bottom.y) bottom = entity.transform.position;
                    if (entity.transform.position.y > top.y) top = entity.transform.position;
                    CleanElevatorKill(entity);
                }
                Elevator elevator = GameManager.server.CreateEntity("assets/prefabs/deployable/elevator/static/elevator.static.prefab", bottom, rot, true) as Elevator;
                elevator.transform.rotation = rot;
                elevator.transform.position = bottom;
                elevator.transform.localPosition += new Vector3(0f, 0.25f, 0f);
                bmgELEVATOR = elevator.gameObject.AddComponent<BMGELEVATOR>();
                elevator.Spawn();
                bmgELEVATOR.Floors = top.y - bottom.y;
                Interface.Oxide.NextTick(() =>
                {
                    if (elevator.IsKilled()) return;
                    RemoveImmortality(elevator.baseProtection, 0.3f, 1.0f, 1.0f, 1.0f, 0.9f, 0.5f, 1.0f, 1.0f, 0.9f, 1.0f, 1.0f, 1.0f, 0.3f, 1.0f, 1.0f, 0.9f, 0.9f, 1.0f, 1.0f, 1.0f, 1.0f, 0.9f, 0.9f, 1.0f, 1.0f);
                    RemoveImmortality(elevator.liftEntity.baseProtection, 0.3f, 1.0f, 1.0f, 1.0f, 0.9f, 0.5f, 1.0f, 1.0f, 0.9f, 1.0f, 1.0f, 1.0f, 0.3f, 1.0f, 1.0f, 0.9f, 0.9f, 1.0f, 1.0f, 1.0f, 1.0f, 0.9f, 0.9f, 1.0f, 1.0f);
                });
                elevator.SetFlag(BaseEntity.Flags.Reserved1, true, false, true);
                elevator.SetFlag(Elevator.Flag_HasPower, true);
                elevator.SendNetworkUpdateImmediate();
                bmgELEVATOR.uid = elevator.net.ID;
                Instance._elevators[elevator.net.ID] = bmgELEVATOR;
                Instance.Subscribe(nameof(OnElevatorButtonPress));
                return elevator;
            }

            internal static void RemoveImmortality(ProtectionProperties baseProtection, float AntiVehicle, float Arrow, float Bite, float Bleeding, float Blunt, float Bullet, float Cold, float ColdExposure, float Collision, float Decay, float Drowned, float ElectricShock, float Explosion, float Fall, float Fun_Water, float Generic, float Heat, float Hunger, float Poison, float Radiation, float RadiationExposure, float Slash, float Stab, float Suicide, float Thirst)
            {
                baseProtection.amounts[(int)DamageType.AntiVehicle] = AntiVehicle;
                baseProtection.amounts[(int)DamageType.Arrow] = Arrow;
                baseProtection.amounts[(int)DamageType.Bite] = Bite;
                baseProtection.amounts[(int)DamageType.Bleeding] = Bleeding;
                baseProtection.amounts[(int)DamageType.Blunt] = Blunt;
                baseProtection.amounts[(int)DamageType.Bullet] = Bullet;
                baseProtection.amounts[(int)DamageType.Cold] = Cold;
                baseProtection.amounts[(int)DamageType.ColdExposure] = ColdExposure;
                baseProtection.amounts[(int)DamageType.Collision] = Collision;
                baseProtection.amounts[(int)DamageType.Decay] = Decay;
                baseProtection.amounts[(int)DamageType.Drowned] = Drowned;
                baseProtection.amounts[(int)DamageType.ElectricShock] = ElectricShock;
                baseProtection.amounts[(int)DamageType.Explosion] = Explosion;
                baseProtection.amounts[(int)DamageType.Fall] = Fall;
                baseProtection.amounts[(int)DamageType.Fun_Water] = Fun_Water;
                baseProtection.amounts[(int)DamageType.Generic] = Generic;
                baseProtection.amounts[(int)DamageType.Heat] = Heat;
                baseProtection.amounts[(int)DamageType.Hunger] = Hunger;
                baseProtection.amounts[(int)DamageType.Poison] = Poison;
                baseProtection.amounts[(int)DamageType.Radiation] = Radiation;
                baseProtection.amounts[(int)DamageType.RadiationExposure] = RadiationExposure;
                baseProtection.amounts[(int)DamageType.Slash] = Slash;
                baseProtection.amounts[(int)DamageType.Stab] = Stab;
                baseProtection.amounts[(int)DamageType.Suicide] = Suicide;
                baseProtection.amounts[(int)DamageType.Thirst] = Thirst;
            }

            public static List<List<BaseEntity>> SplitElevators(List<BaseEntity> source)
            {
                var result = new List<List<BaseEntity>>();
                List<int> Elevators = new List<int>();
                foreach (BaseEntity entity in source)
                {
                    int distance = (int)(entity.transform.position.x + entity.transform.position.x);
                    if (!Elevators.Contains(distance))
                    {
                        Elevators.Add(distance);
                        result.Add(new List<BaseEntity>
                        {
                            entity
                        });
                    }
                    else
                    {
                        int index = Elevators.IndexOf(distance);
                        result[index].Add(entity);
                    }
                }
                return result;
            }

            private HashSet<ulong> _granted = new HashSet<ulong>();

            public bool HasCardPermission(BasePlayer player)
            {
                if (_granted.Contains(player.userID) || options.RequiredAccessLevel == 0 || player.HasPermission("raidablebases.elevators.bypass.card"))
                {
                    return true;
                }

                string shortname = options.RequiredAccessLevel == 1 ? "keycard_green" : options.RequiredAccessLevel == 2 ? "keycard_blue" : "keycard_red";

                Item item = player.inventory.FindItemID(shortname);

                if (item == null || item.skin != options.SkinID)
                {
                    raid.TryMessage(player, options.RequiredAccessLevel == 1 ? "Elevator Green Card" : options.RequiredAccessLevel == 2 ? "Elevator Blue Card" : options.RequiredAccessLevel == 3 ? "Elevator Red Card" : "Elevator Special Card");
                    return false;
                }

                Keycard keycard = item.GetHeldEntity() as Keycard;

                if (keycard?.accessLevel == options.RequiredAccessLevel)
                {
                    if (options.RequiredAccessLevelOnce)
                    {
                        _granted.Add(player.userID);
                    }

                    return true;
                }

                raid.TryMessage(player, options.RequiredAccessLevel == 1 ? "Elevator Green Card" : options.RequiredAccessLevel == 2 ? "Elevator Blue Card" : options.RequiredAccessLevel == 3 ? "Elevator Red Card" : "Elevator Special Card");
                return false;
            }

            public bool HasBuildingPermission(BasePlayer player)
            {
                if (!options.RequiresBuildingPermission || player.HasPermission("raidablebases.elevators.bypass.building"))
                {
                    return true;
                }

                if (Time.time < lastPermissionTime)
                {
                    return false;
                }

                lastPermissionTime = Time.time + 1f;

                if (player.IsBuildingBlocked())
                {
                    raid.TryMessage(player, "Elevator Privileges");
                    return false;
                }

                return true;
            }
        }

        public class RaidableSpawns
        {
            public HashSet<RaidableSpawnLocation> Spawns { get; set; } = new HashSet<RaidableSpawnLocation>();
            public Dictionary<CacheType, HashSet<RaidableSpawnLocation>> Cached { get; set; } = new Dictionary<CacheType, HashSet<RaidableSpawnLocation>>();
            private float lastTryTime;
            public bool IsCustomSpawn { get; set; }

            public HashSet<RaidableSpawnLocation> Inactive(CacheType cacheType) => GetCache(cacheType);

            public RaidableSpawns(HashSet<RaidableSpawnLocation> spawns)
            {
                Spawns = spawns;
                IsCustomSpawn = true;
            }

            public RaidableSpawns() { }

            public bool CanBuild(BasePlayer player, Vector3 buildPos, float radius)
            {
                if (IsCustomSpawn)
                {
                    foreach (var rsl in Spawns)
                    {
                        if (InRange(rsl.Location, buildPos, radius))
                        {
                            return false;
                        }
                    }
                }
                return true;
            }

            public bool Add(RaidableSpawnLocation rsl, CacheType cacheType, HashSet<RaidableSpawnLocation> cache, bool forced)
            {
                if (!forced)
                {
                    switch (cacheType)
                    {
                        case CacheType.Submerged:
                            rsl.WaterHeight = TerrainMeta.WaterMap.GetHeight(rsl.Location);
                            rsl.Surroundings.Clear();
                            break;
                        case CacheType.Generic:
                            if (Instance.EventTerritory(rsl.Location))
                            {
                                return false;
                            }
                            break;
                        case CacheType.Close:
                            if (RaidableBase.IsTooClose(rsl.Location, GetDistance(RaidableType.None)))
                            {
                                return false;
                            }
                            break;
                    }
                }

                return Spawns.Add(rsl);
            }

            public void Check()
            {
                if (lastTryTime == 0f || Time.time - lastTryTime > 600f)
                {
                    TryAddRange(CacheType.Temporary, true);
                    TryAddRange(CacheType.Privilege, true);
                    lastTryTime = Time.time;
                }

                if (Spawns.Count == 0)
                {
                    TryAddRange();
                }
            }

            public void TryAddRange(CacheType cacheType = CacheType.Generic, bool forced = false)
            {
                HashSet<RaidableSpawnLocation> cache = GetCache(cacheType);
                List<RaidableSpawnLocation> remove = new List<RaidableSpawnLocation>();

                foreach (var rsl in cache)
                {
                    if (Add(rsl, cacheType, cache, forced))
                    {
                        remove.Add(rsl);
                    }
                }

                remove.ForEach(rsl => cache.Remove(rsl));
            }

            public RaidableSpawnLocation GetRandom(BuildingWaterOptions options)
            {
                RaidableSpawnLocation rsl = Spawns.GetRandom();

                Remove(rsl, CacheType.Generic);

                return rsl;
            }

            public HashSet<RaidableSpawnLocation> GetCache(CacheType cacheType)
            {
                HashSet<RaidableSpawnLocation> cache;
                if (!Cached.TryGetValue(cacheType, out cache))
                {
                    Cached[cacheType] = cache = new HashSet<RaidableSpawnLocation>();
                }
                return cache;
            }

            public void AddNear(Vector3 target, float radius, CacheType cacheType, float delayTime)
            {
                if (delayTime > 0)
                {
                    Instance.timer.Once(delayTime, () => AddNear(target, radius, cacheType, 0f));
                    return;
                }

                HashSet<RaidableSpawnLocation> cache = GetCache(cacheType);
                List<RaidableSpawnLocation> remove = new List<RaidableSpawnLocation>();

                foreach (var rsl in cache)
                {
                    if (InRange2D(target, rsl.Location, radius) && Spawns.Add(rsl))
                    {
                        remove.Add(rsl);
                    }
                }

                remove.ForEach(rsl => cache.Remove(rsl));
            }

            public void Remove(RaidableSpawnLocation a, CacheType cacheType)
            {
                GetCache(cacheType).Add(a);
                Spawns.Remove(a);
            }

            public float RemoveNear(Vector3 target, float radius, CacheType cacheType, RaidableType type)
            {
                if (cacheType == CacheType.Generic)
                {
                    radius = Mathf.Max(GetDistance(type), radius);
                }

                HashSet<RaidableSpawnLocation> cache = GetCache(cacheType);
                List<RaidableSpawnLocation> remove = new List<RaidableSpawnLocation>();

                foreach (var rsl in Spawns)
                {
                    if (InRange2D(target, rsl.Location, radius) && cache.Add(rsl))
                    {
                        remove.Add(rsl);
                    }
                }

                remove.ForEach(rsl => Spawns.Remove(rsl));

                return radius;
            }
        }

        public class PlayerInfo
        {
            public int Raids, TotalRaids;
            public DateTime ExpiredDate { get; set; } = DateTime.MinValue;
            public bool IsExpired()
            {
                if (ExpiredDate == DateTime.MinValue)
                {
                    ResetExpiredDate();
                }

                return ExpiredDate < DateTime.Now;
            }
            public void ResetExpiredDate() => ExpiredDate = DateTime.Now.AddDays(60);
            public static PlayerInfo Get(string userid)
            {
                PlayerInfo playerInfo;
                if (!data.Players.TryGetValue(userid, out playerInfo))
                {
                    data.Players[userid] = playerInfo = new PlayerInfo();
                }
                return playerInfo;
            }
            public void Reset()
            {
                Raids = 0;
            }
            [JsonIgnore]
            public bool Any => Raids > 0;
        }

        public class RotationCycle
        {
            private List<string> keyList = new List<string>();

            public void Add(RaidableType type, string key)
            {
                if (!config.Settings.Management.RequireAllSpawned || type == RaidableType.Grid || type == RaidableType.Manual)
                {
                    return;
                }

                if (!keyList.Contains(key))
                {
                    keyList.Add(key);
                }
            }

            public bool CanSpawn(RaidableType type, string key)
            {
                if (!config.Settings.Management.RequireAllSpawned || type == RaidableType.Grid || type == RaidableType.Manual)
                {
                    return true;
                }

                if (!keyList.Contains(key))
                {
                    return true;
                }

                return TryClear(type);
            }

            public bool TryClear(RaidableType type)
            {
                foreach (var profile in Instance.Buildings.Profiles)
                {
                    if (MustExclude(type, profile.Value.Options.AllowPVP))
                    {
                        continue;
                    }

                    if (!keyList.Contains(profile.Key) && FileExists(profile.Key))
                    {
                        return false;
                    }

                    if (profile.Value.Options.AdditionalBases.Exists(kvp => !keyList.Contains(kvp.Key) && FileExists(kvp.Key)))
                    {
                        return false;
                    }
                }

                keyList.Clear();
                return true;
            }
        }

        public class PlayerInputEx : FacepunchBehaviour
        {
            public BasePlayer player { get; set; }
            private InputState input { get; set; }
            private RaidableBase raid { get; set; }
            private ulong userID { get; set; }
            private Vector3 lastPosition { get; set; }
            private Raider raider { get; set; }
            private Transform _transform { get; set; }
            private Dictionary<ItemDefinition, string> definitions { get; set; }
            private bool isDestroyed;

            private void Awake()
            {
                gameObject.name = "PlayerInputEx";
                player = GetComponent<BasePlayer>();
                _transform = player.transform;
                lastPosition = _transform.position;
                input = player.serverInput;
                userID = player.userID;
            }

            private void OnDestroy()
            {
                if (!player.IsReallyConnected())
                {
                    raid?.intruders?.Remove(userID);
                }
                if (!isDestroyed)
                {
                    try { CancelInvoke(Repeater); } catch { }
                }
                isDestroyed = true;
                Destroy(this);
            }

            public void Setup(RaidableBase raid)
            {
                this.definitions = Instance._definitions;
                this.raid = raid;
                raider = raid.GetRaider(player);
                raider.Input = this;
                raider.lastActiveTime = Time.time;
                InvokeRepeating(Repeater, 0f, 0.1f);
            }

            public void Restart()
            {
                CancelInvoke(Repeater);
                InvokeRepeating(Repeater, 0.1f, 0.1f);
            }

            private void Repeater()
            {
                if (isDestroyed)
                {
                    return;
                }
                if (raid == null || !player.IsReallyConnected() || player.IsDead())
                {
                    isDestroyed = true;
                    try { CancelInvoke(Repeater); } catch { }
                    raid?.OnPlayerExit(player, true);
                    raid?.intruders.Remove(userID);
                    Destroy(this);
                    return;
                }
                if (_transform.position != lastPosition)
                {
                    lastPosition = _transform.position;
                    raider.lastActiveTime = Time.time;
                }
                if (config.Settings.Management.AllowLadders)
                {
                    TryPlace(ConstructionType.Any);
                }
            }

            public bool TryPlace(ConstructionType constructionType)
            {
                if (player.svActiveItemID.Value == 0)
                {
                    return false;
                }

                var input = player.serverInput;

                if (!input.WasJustReleased(BUTTON.FIRE_PRIMARY) && !input.IsDown(BUTTON.FIRE_PRIMARY))
                {
                    return false;
                }

                Item item = player.GetActiveItem();

                if (item == null)
                {
                    return false;
                }

                RaycastHit hit;
                if (!IsConstructionType(item.info.shortname, ref constructionType, out hit))
                {
                    return false;
                }

                int amount = item.amount;

                var action = new Action(() =>
                {
                    if (raid == null || item == null || item.amount != amount || IsConstructionNear(constructionType, hit.point))
                    {
                        return;
                    }

                    Quaternion rot;
                    if (constructionType == ConstructionType.Barricade)
                    {
                        rot = Quaternion.LookRotation((_transform.position.WithY(0f) - hit.point.WithY(0f)).normalized);
                    }
                    else rot = Quaternion.LookRotation(hit.normal, Vector3.up);

                    string prefab;
                    if (!definitions.TryGetValue(item.info, out prefab))
                    {
                        return;
                    }

                    var e = GameManager.server.CreateEntity(prefab, hit.point, rot, true);

                    if (e.IsNull())
                    {
                        return;
                    }

                    e.gameObject.SendMessage("SetDeployedBy", player, SendMessageOptions.DontRequireReceiver);
                    e.OwnerID = 0;
                    e.Spawn();
                    item.UseItem(1);

                    if (constructionType == ConstructionType.Ladder)
                    {
                        e.SetParent(hit.GetEntity(), true, false);
                    }

                    raid.MyInstance.RaidEntities[e.net.ID] = new RaidEntity(raid, e);
                    raid.BuiltList[e] = hit.point;
                    raid.AddEntity(e);
                });

                player.Invoke(action, 0.1f);
                return true;
            }

            public bool IsConstructionType(string shortname, ref ConstructionType constructionType, out RaycastHit hit)
            {
                hit = default(RaycastHit);

                if (constructionType == ConstructionType.Any || constructionType == ConstructionType.Ladder)
                {
                    if (shortname == "ladder.wooden.wall")
                    {
                        constructionType = ConstructionType.Ladder;

                        if (raid.Options.RequiresCupboardAccessLadders && !raid.CanBuild(player))
                        {
                            Message(player, "Ladders Require Building Privilege!");
                            return false;
                        }

                        if (!Physics.Raycast(player.eyes.HeadRay(), out hit, 4f, Layers.Mask.Construction, QueryTriggerInteraction.Ignore))
                        {
                            return false;
                        }

                        var entity = hit.GetEntity();

                        if (entity.IsNull() || entity.OwnerID != 0 || !Instance.Blocks.Contains(entity.ShortPrefabName)) // walls, foundations and floors
                        {
                            return false;
                        }

                        return true;
                    }
                }

                if (constructionType == ConstructionType.Any || constructionType == ConstructionType.Barricade)
                {
                    if (shortname.StartsWith("barricade."))
                    {
                        constructionType = ConstructionType.Barricade;

                        if (!Physics.Raycast(player.eyes.HeadRay(), out hit, 5f, targetMask, QueryTriggerInteraction.Ignore))
                        {
                            return false;
                        }

                        return hit.GetEntity().IsNull();
                    }
                }

                return false;
            }

            private bool IsConstructionNear(ConstructionType constructionType, Vector3 target)
            {
                float radius = constructionType == ConstructionType.Barricade ? 1f : 0.3f;
                int layerMask = constructionType == ConstructionType.Barricade ? -1 : Layers.Mask.Deployed;
                var entities = FindEntitiesOfType<BaseEntity>(target, radius, layerMask);
                bool result;
                if (constructionType == ConstructionType.Barricade)
                {
                    result = entities.Count > 0;
                }
                else result = entities.Exists(e => e is BaseLadder);
                return result;
            }
        }

        public class HumanoidBrain : ScientistBrain
        {
            internal enum AttackType
            {
                BaseProjectile,
                FlameThrower,
                Melee,
                Water,
                None
            }

            internal string displayName;
            internal ScientistNPC npc;
            private AttackEntity _attackEntity;
            private FlameThrower flameThrower;
            private LiquidWeapon liquidWeapon;
            private BaseMelee baseMelee;
            private BasePlayer AttackTarget;
            internal RaidableBase raid;
            internal NpcSettings Settings;
            private List<Vector3> positions;
            internal Vector3 DestinationOverride;
            internal bool isMurderer;
            internal ulong uid;
            private float lastWarpTime;
            internal float softLimitSenseRange;
            private float nextAttackTime;
            private float attackRange;
            private float attackCooldown;
            internal AttackType attackType = AttackType.None;
            private BaseNavigator.NavigationSpeed CurrentSpeed = BaseNavigator.NavigationSpeed.Normal;

            internal Vector3 AttackPosition => AttackTarget.ServerPosition;

            internal Vector3 ServerPosition => npc.ServerPosition;

            internal AttackEntity AttackEntity
            {
                get
                {
                    if (_attackEntity.IsNull())
                    {
                        IdentifyWeapon();
                    }

                    return _attackEntity;
                }
            }

            internal void IdentifyWeapon()
            {
                _attackEntity = GetEntity().GetAttackEntity();

                attackRange = 0f;
                attackCooldown = 99999f;
                attackType = AttackType.None;
                baseMelee = null;
                flameThrower = null;
                liquidWeapon = null;

                if (_attackEntity.IsNull())
                {
                    return;
                }

                switch (_attackEntity.ShortPrefabName)
                {
                    case "double_shotgun.entity":
                    case "shotgun_pump.entity":
                    case "shotgun_waterpipe.entity":
                    case "spas12.entity":
                        SetAttackRestrictions(AttackType.BaseProjectile, 30f, 0f, 30f);
                        break;
                    case "ak47u.entity":
                    case "ak47u_ice.entity":
                    case "bolt_rifle.entity":
                    case "glock.entity":
                    case "hmlmg.entity":
                    case "l96.entity":
                    case "lr300.entity":
                    case "m249.entity":
                    case "m39.entity":
                    case "m92.entity":
                    case "mp5.entity":
                    case "nailgun.entity":
                    case "pistol_eoka.entity":
                    case "pistol_revolver.entity":
                    case "pistol_semiauto.entity":
                    case "python.entity":
                    case "semi_auto_rifle.entity":
                    case "thompson.entity":
                    case "smg.entity":
                        SetAttackRestrictions(AttackType.BaseProjectile, 300f, 0f, 150f);
                        break;
                    case "snowballgun.entity":
                        SetAttackRestrictions(AttackType.BaseProjectile, 15f, 0.1f, 15f);
                        break;
                    case "chainsaw.entity":
                    case "jackhammer.entity":
                        baseMelee = _attackEntity as BaseMelee;
                        SetAttackRestrictions(AttackType.Melee, 2.5f, (_attackEntity.animationDelay + _attackEntity.deployDelay) * 2f);
                        break;
                    case "axe_salvaged.entity":
                    case "bone_club.entity":
                    case "butcherknife.entity":
                    case "candy_cane.entity":
                    case "hammer_salvaged.entity":
                    case "hatchet.entity":
                    case "icepick_salvaged.entity":
                    case "knife.combat.entity":
                    case "knife_bone.entity":
                    case "longsword.entity":
                    case "mace.entity":
                    case "machete.weapon":
                    case "pickaxe.entity":
                    case "pitchfork.entity":
                    case "salvaged_cleaver.entity":
                    case "salvaged_sword.entity":
                    case "sickle.entity":
                    case "spear_stone.entity":
                    case "spear_wooden.entity":
                    case "stone_pickaxe.entity":
                    case "stonehatchet.entity":
                        baseMelee = _attackEntity as BaseMelee;
                        SetAttackRestrictions(AttackType.Melee, 2.5f, _attackEntity.animationDelay + _attackEntity.deployDelay);
                        break;
                    case "flamethrower.entity":
                        flameThrower = _attackEntity as FlameThrower;
                        SetAttackRestrictions(AttackType.FlameThrower, 10f, (_attackEntity.animationDelay + _attackEntity.deployDelay) * 2f);
                        break;
                    case "compound_bow.entity":
                    case "crossbow.entity":
                    case "speargun.entity":
                        SetAttackRestrictions(AttackType.BaseProjectile, 200f, (_attackEntity.animationDelay + _attackEntity.deployDelay) * 1.25f, 150f);
                        break;
                    case "watergun.entity":
                    case "waterpistol.entity":
                        liquidWeapon = _attackEntity as LiquidWeapon;
                        liquidWeapon.AutoPump = true;
                        SetAttackRestrictions(AttackType.Water, 10f, 2f);
                        break;
                    default: _attackEntity = null; break;
                }
            }

            private void SetAttackRestrictions(AttackType attackType, float attackRange, float attackCooldown, float effectiveRange = 0f)
            {
                if (effectiveRange != 0f)
                {
                    _attackEntity.effectiveRange = effectiveRange;
                }

                this.attackType = attackType;
                this.attackRange = attackRange;
                this.attackCooldown = attackCooldown;
            }

            public bool ValidTarget
            {
                get
                {
                    if (AttackTarget.IsKilled() || ShouldForgetTarget(AttackTarget))
                    {
                        return false;
                    }

                    return true;
                }
            }

            public override void OnDestroy()
            {
                if (!Rust.Application.isQuitting)
                {
                    BaseEntity.Query.Server.RemoveBrain(GetEntity());
                    LeaveGroup();
                }

                Instance?.HumanoidBrains?.Remove(uid);
                try { CancelInvoke(); } catch { }
            }

            public override void InitializeAI()
            {
                base.InitializeAI();
                base.ForceSetAge(0f);

                Pet = false;
                sleeping = false;
                UseAIDesign = true;
                AllowedToSleep = false;
                HostileTargetsOnly = false;
                AttackRangeMultiplier = 2f;
                MaxGroupSize = 0;

                Senses.Init(
                    owner: GetEntity(),
                    brain: this,
                    memoryDuration: 5f,
                    range: 50f,
                    targetLostRange: 75f,
                    visionCone: -1f,
                    checkVision: false,
                    checkLOS: true,
                    ignoreNonVisionSneakers: true,
                    listenRange: 15f,
                    hostileTargetsOnly: false,
                    senseFriendlies: false,
                    ignoreSafeZonePlayers: false,
                    senseTypes: EntityType.Player,
                    refreshKnownLOS: true
                );

                CanUseHealingItems = true;
            }

            public override void AddStates()
            {
                base.AddStates();

                states[AIState.Attack] = new AttackState(this);
            }

            public class AttackState : BaseAttackState
            {
                private new HumanoidBrain brain;
                private global::HumanNPC npc;

                private IAIAttack attack => brain.Senses.ownerAttack;

                public AttackState(HumanoidBrain humanoidBrain)
                {
                    base.brain = brain = humanoidBrain;
                    base.AgrresiveState = true;
                    npc = brain.GetBrainBaseEntity() as global::HumanNPC;
                }

                public override void StateEnter(BaseAIBrain _brain, BaseEntity _entity)
                {
                    if (brain.ValidTarget)
                    {
                        if (InAttackRange())
                        {
                            StartAttacking();
                        }
                        if (brain.Navigator.CanUseNavMesh)
                        {
                            brain.Navigator.SetDestination(brain.DestinationOverride, BaseNavigator.NavigationSpeed.Fast, 0f, 0f);
                        }
                    }
                }

                public override void StateLeave(BaseAIBrain _brain, BaseEntity _entity)
                {

                }

                private void StopAttacking()
                {
                    if (attack != null)
                    {
                        attack.StopAttacking();
                        brain.AttackTarget = null;
                        brain.Navigator.ClearFacingDirectionOverride();
                    }
                }

                public override StateStatus StateThink(float delta, BaseAIBrain _brain, BaseEntity _entity)
                {
                    if (attack == null)
                    {
                        return StateStatus.Error;
                    }
                    if (!brain.ValidTarget)
                    {
                        StopAttacking();

                        return StateStatus.Finished;
                    }
                    if (brain.Senses.ignoreSafeZonePlayers && brain.AttackTarget.InSafeZone())
                    {
                        return StateStatus.Error;
                    }
                    if (brain.Navigator.CanUseNavMesh && !brain.Navigator.SetDestination(brain.DestinationOverride, BaseNavigator.NavigationSpeed.Fast, 0f, 0f))
                    {
                        return StateStatus.Error;
                    }
                    if (!brain.CanLeave(brain.AttackPosition) || !brain.CanShoot())
                    {
                        brain.Forget();

                        StopAttacking();

                        return StateStatus.Finished;
                    }
                    if (InAttackRange())
                    {
                        StartAttacking();
                    }
                    return StateStatus.Running;
                }

                private bool InAttackRange()
                {
                    if (npc.IsWounded())
                    {
                        return false;
                    }
                    return attack.CanAttack(brain.AttackTarget) && brain.IsInAttackRange() && brain.CanSeeTarget(brain.AttackTarget);
                }

                private void StartAttacking()
                {
                    brain.SetAimDirection();

                    if (!brain.CanShoot() || brain.IsAttackOnCooldown())
                    {
                        return;
                    }

                    if (brain.attackType == AttackType.BaseProjectile)
                    {
                        npc.ShotTest(brain.AttackPosition.Distance(brain.ServerPosition));
                    }
                    else if (brain.attackType == AttackType.FlameThrower)
                    {
                        brain.UseFlameThrower();
                    }
                    else if (brain.attackType == AttackType.Water)
                    {
                        brain.UseWaterGun();
                    }
                    else brain.MeleeAttack();
                }
            }

            private bool init;

            public void Init()
            {
                if (init) return;
                init = true;
                lastWarpTime = Time.time;
                npc.spawnPos = raid.Location;
                npc.AdditionalLosBlockingLayer = visibleMask;
                IdentifyWeapon();
                SetupNavigator(GetEntity(), GetComponent<BaseNavigator>(), raid.ProtectionRadius);
            }

            private void Converge()
            {
                foreach (var brain in Instance.HumanoidBrains.Values)
                {
                    if (brain != null && brain != this && brain.attackType == attackType && brain.CanConverge(npc) && CanLeave(AttackPosition))
                    {
                        brain.SetTarget(AttackTarget, false);
                    }
                }
            }

            public void Forget()
            {
                Senses.Players.Clear();
                Senses.Memory.All.Clear();
                Senses.Memory.Threats.Clear();
                Senses.Memory.Targets.Clear();
                Senses.Memory.Players.Clear();
                Navigator.ClearFacingDirectionOverride();

                DestinationOverride = GetRandomRoamPosition();
                SenseRange = ListenRange = Settings.AggressionRange;
                Senses.targetLostRange = TargetLostRange = SenseRange * 1.25f;
                AttackTarget = null;

                TryReturnHome();
            }

            private void RandomMove(float radius)
            {
                var to = AttackPosition + UnityEngine.Random.onUnitSphere * radius;

                to.y = TerrainMeta.HeightMap.GetHeight(to);

                SetDestination(to);
            }

            public void SetupNavigator(BaseCombatEntity owner, BaseNavigator navigator, float distance)
            {
                navigator.CanUseNavMesh = !Rust.Ai.AiManager.nav_disable;
                navigator.MaxRoamDistanceFromHome = navigator.BestMovementPointMaxDistance = navigator.BestRoamPointMaxDistance = distance * 0.85f;
                navigator.DefaultArea = "Walkable";
                navigator.topologyPreference = ((TerrainTopology.Enum)TerrainTopology.EVERYTHING);
                navigator.Agent.agentTypeID = NavMesh.GetSettingsByIndex(1).agentTypeID; // -1372625422
                navigator.MaxWaterDepth = config.Settings.Management.WaterDepth;

                if (navigator.CanUseNavMesh)
                {
                    navigator.Init(owner, navigator.Agent);
                }
            }

            public Vector3 GetAimDirection()
            {
                if (Navigator.IsOverridingFacingDirection)
                {
                    return Navigator.FacingDirectionOverride;
                }
                if (InRange2D(AttackPosition, ServerPosition, 1f))
                {
                    return npc.eyes.BodyForward();
                }
                return (AttackPosition - ServerPosition).normalized;
            }

            private void SetAimDirection()
            {
                Navigator.SetFacingDirectionEntity(AttackTarget);
                npc.SetAimDirection(GetAimDirection());
            }

            private void SetDestination()
            {
                SetDestination(GetRandomRoamPosition());
            }

            private void SetDestination(Vector3 destination)
            {
                if (!CanLeave(destination))
                {
                    if (attackType != AttackType.BaseProjectile)
                    {
                        destination = ((destination.XZ3D() - raid.Location.XZ3D()).normalized * (raid.ProtectionRadius * 0.75f)) + raid.Location;

                        destination += UnityEngine.Random.onUnitSphere * (raid.ProtectionRadius * 0.2f);
                    }
                    else
                    {
                        destination = GetRandomRoamPosition();
                    }

                    CurrentSpeed = BaseNavigator.NavigationSpeed.Normal;
                }

                if (destination != DestinationOverride)
                {
                    destination.y = TerrainMeta.HeightMap.GetHeight(destination);

                    DestinationOverride = destination;
                }

                Navigator.SetCurrentSpeed(CurrentSpeed);

                if (Navigator.CurrentNavigationType == BaseNavigator.NavigationType.None && !Rust.Ai.AiManager.ai_dormant && !Rust.Ai.AiManager.nav_disable)
                {
                    Navigator.SetCurrentNavigationType(BaseNavigator.NavigationType.NavMesh);
                }

                if (Navigator.Agent == null || !Navigator.CanUseNavMesh || !Navigator.SetDestination(destination, CurrentSpeed))
                {
                    Navigator.Destination = destination;
                    npc.finalDestination = destination;
                }
            }

            public void SetTarget(BasePlayer player, bool converge = true)
            {
                if (npc.IsKilled() || raid == null)
                {
                    Destroy(this);
                    return;
                }

                if (player.IsKilled() || AttackTarget == player)
                {
                    return;
                }

                if (npc.lastGunShotTime < Time.time + 2f)
                {
                    npc.nextTriggerTime = Time.time + 0.2f;
                    nextAttackTime = Time.realtimeSinceStartup + 0.2f;
                }

                TrySetKnown(player);
                npc.lastAttacker = player;
                AttackTarget = player;

                if (!IsInSenseRange(player.transform.position))
                {
                    SenseRange = ListenRange = Settings.AggressionRange + player.transform.position.Distance(ServerPosition);
                    TargetLostRange = SenseRange + (SenseRange * 0.25f);
                }
                else
                {
                    SenseRange = ListenRange = softLimitSenseRange;
                    TargetLostRange = softLimitSenseRange * 1.25f;
                }

                if (converge)
                {
                    Converge();
                }
            }

            private void TryReturnHome()
            {
                if (Settings.CanLeave && !IsInHomeRange())
                {
                    CurrentSpeed = BaseNavigator.NavigationSpeed.Normal;

                    Warp();
                }
            }

            private void TryToAttack() => TryToAttack(null);

            private void TryToAttack(BasePlayer attacker)
            {
                if (attacker.IsNull())
                {
                    attacker = GetBestTarget();
                }

                if (attacker.IsNull())
                {
                    return;
                }

                if (ShouldForgetTarget(attacker))
                {
                    Forget();

                    return;
                }

                SetTarget(attacker);

                if (!CanSeeTarget(attacker))
                {
                    return;
                }

                if (attackType == AttackType.BaseProjectile)
                {
                    TryScientistActions();
                }
                else
                {
                    TryMurdererActions();
                }

                SwitchToState(AIState.Attack, -1);
            }

            private void TryMurdererActions()
            {
                CurrentSpeed = BaseNavigator.NavigationSpeed.Fast;

                if (!IsInReachableRange())
                {
                    RandomMove(15f);
                }
                else if (!IsInAttackRange())
                {
                    if (attackType == AttackType.FlameThrower)
                    {
                        RandomMove(attackRange);
                    }
                    else
                    {
                        SetDestination(AttackPosition);
                    }
                }
            }

            private void TryScientistActions()
            {
                CurrentSpeed = BaseNavigator.NavigationSpeed.Fast;

                SetDestination();
            }

            public void SetupMovement(List<Vector3> positions)
            {
                this.positions = positions;

                InvokeRepeating(TryToRoam, 0f, 7.5f);
                InvokeRepeating(TryToAttack, 1f, 1f);
            }

            private void TryToRoam()
            {
                if (Settings.KillUnderwater && npc.IsSwimming())
                {
                    npc.Kill();
                    Destroy(this);
                    return;
                }

                if (ValidTarget)
                {
                    return;
                }

                if (IsStuck())
                {
                    Warp();

                    Navigator.stuckTimer = 0f;
                }

                CurrentSpeed = BaseNavigator.NavigationSpeed.Normal;

                SetDestination();
            }

            private bool IsStuck() => false; //InRange(npc.transform.position, Navigator.stuckCheckPosition, Navigator.StuckDistance);

            public void Warp()
            {
                if (Time.time < lastWarpTime)
                {
                    return;
                }

                lastWarpTime = Time.time + 1f;

                DestinationOverride = GetRandomRoamPosition();

                Navigator.Warp(DestinationOverride);
            }

            private void UseFlameThrower()
            {
                if (flameThrower.ammo < flameThrower.maxAmmo * 0.25)
                {
                    flameThrower.SetFlameState(false);
                    flameThrower.ServerReload();
                    return;
                }
                npc.triggerEndTime = Time.time + attackCooldown;
                flameThrower.SetFlameState(true);
                flameThrower.Invoke(() => flameThrower.SetFlameState(false), 2f);
            }

            private void UseWaterGun()
            {
                RaycastHit hit;
                if (Physics.Raycast(npc.eyes.BodyRay(), out hit, 10f, 1218652417))
                {
                    List<DamageTypeEntry> damage = new List<DamageTypeEntry>();
                    WaterBall.DoSplash(hit.point, 2f, ItemManager.FindItemDefinition("water"), 10);
                    DamageUtil.RadiusDamage(npc, liquidWeapon.LookupPrefab(), hit.point, 0.15f, 0.15f, damage, 131072, true);
                }
            }

            private void UseChainsaw()
            {
                AttackEntity.TopUpAmmo();
                AttackEntity.ServerUse();
                AttackTarget.Hurt(10f * AttackEntity.npcDamageScale, DamageType.Bleeding, npc);
            }

            private void MeleeAttack()
            {
                if (baseMelee.IsNull())
                {
                    return;
                }

                if (AttackEntity is Chainsaw)
                {
                    UseChainsaw();
                    return;
                }

                Vector3 position = AttackPosition;
                AttackEntity.StartAttackCooldown(AttackEntity.repeatDelay * 2f);
                npc.SignalBroadcast(BaseEntity.Signal.Attack, string.Empty, null);
                if (baseMelee.swingEffect.isValid)
                {
                    Effect.server.Run(baseMelee.swingEffect.resourcePath, position, Vector3.forward, npc.Connection, false);
                }
                HitInfo hitInfo = new HitInfo
                {
                    damageTypes = new DamageTypeList(),
                    DidHit = true,
                    Initiator = npc,
                    HitEntity = AttackTarget,
                    HitPositionWorld = position,
                    HitPositionLocal = AttackTarget.transform.InverseTransformPoint(position),
                    HitNormalWorld = npc.eyes.BodyForward(),
                    HitMaterial = StringPool.Get("Flesh"),
                    PointStart = ServerPosition,
                    PointEnd = position,
                    Weapon = AttackEntity,
                    WeaponPrefab = AttackEntity
                };

                hitInfo.damageTypes.Set(DamageType.Slash, baseMelee.TotalDamage() * AttackEntity.npcDamageScale);
                Effect.server.ImpactEffect(hitInfo);
                AttackTarget.OnAttacked(hitInfo);
            }

            private bool CanConverge(global::HumanNPC other)
            {
                if (ValidTarget && !ShouldForgetTarget(AttackTarget)) return false;
                if (other.IsKilled() || other.IsDead()) return false;
                return IsInTargetRange(other.transform.position);
            }

            private bool CanLeave(Vector3 destination)
            {
                return Settings.CanLeave || IsInLeaveRange(destination);
            }

            private bool CanSeeTarget(BasePlayer target)
            {
                if (Navigator.CurrentNavigationType == BaseNavigator.NavigationType.None && (attackType == AttackType.FlameThrower || attackType == AttackType.Melee))
                {
                    return true;
                }

                if (ServerPosition.Distance(target.ServerPosition) < 10f || Senses.Memory.IsLOS(target))
                {
                    return true;
                }

                nextAttackTime = Time.realtimeSinceStartup + 1f;

                return false;
            }

            public bool CanRoam(Vector3 destination)
            {
                return destination == DestinationOverride && IsInSenseRange(destination);
            }

            private bool CanShoot()
            {
                if (attackType == AttackType.None)
                {
                    return false;
                }

                return Settings.CanShoot || attackType != AttackType.BaseProjectile || IsInLeaveRange(AttackPosition);
            }

            private void TrySetKnown(BasePlayer player)
            {
                if (Senses.ownerAttack != null && !Senses.Memory.IsPlayerKnown(player) && !Senses.Memory.Targets.Contains(player))
                {
                    Senses.Memory.SetKnown(player, npc, Senses);
                }
            }

            public BasePlayer GetBestTarget()
            {
                if (npc.IsWounded())
                {
                    return null;
                }
                float delta = -1f;
                BasePlayer target = null;
                foreach (var player in Senses.Memory.Targets.OfType<BasePlayer>())
                {
                    if (ShouldForgetTarget(player) || !player.IsHuman() && !config.Settings.Management.TargetNpcs) continue;
                    float dist = player.transform.position.Distance(npc.transform.position);
                    float rangeDelta = 1f - Mathf.InverseLerp(1f, SenseRange, dist);
                    rangeDelta += (CanSeeTarget(player) ? 2f : 0f);
                    if (rangeDelta <= delta) continue;
                    target = player;
                    delta = rangeDelta;
                }
                return target;
            }

            private Vector3 GetRandomRoamPosition()
            {
                return positions.GetRandom();
            }

            private bool IsAttackOnCooldown()
            {
                if (attackType == AttackType.None || Time.realtimeSinceStartup < nextAttackTime)
                {
                    return true;
                }

                if (attackCooldown > 0f)
                {
                    nextAttackTime = Time.realtimeSinceStartup + attackCooldown;
                }

                return false;
            }

            private bool IsInAttackRange(float range = 0f)
            {
                return InRange(ServerPosition, AttackPosition, range == 0f ? attackRange : range);
            }

            private bool IsInHomeRange()
            {
                return InRange(ServerPosition, raid.Location, Mathf.Max(raid.ProtectionRadius, TargetLostRange));
            }

            private bool IsInLeaveRange(Vector3 destination)
            {
                return InRange(raid.Location, destination, raid.ProtectionRadius);
            }

            private bool IsInReachableRange()
            {
                if (AttackPosition.y - ServerPosition.y > attackRange)
                {
                    return false;
                }

                return attackType != AttackType.Melee || InRange(AttackPosition, ServerPosition, 15f);
            }

            private bool IsInSenseRange(Vector3 destination)
            {
                return InRange2D(raid.Location, destination, SenseRange);
            }

            private bool IsInTargetRange(Vector3 destination)
            {
                return InRange2D(raid.Location, destination, TargetLostRange);
            }

            private bool ShouldForgetTarget(BasePlayer target)
            {
                return target.IsNull() || target.health <= 0f || target.limitNetworking || target.IsDead() || !IsInTargetRange(target.transform.position);
            }
        }

        public class Raider
        {
            public ulong userid;
            public string id;
            public string displayName;
            public bool reward = true;
            public bool IsRaider;
            public bool IsAlly;
            public bool IsAllowed;
            public bool PreEnter = true;
            public bool LockedOnEnter;
            public PlayerInputEx Input;
            public float lastActiveTime;
            private BasePlayer _player;
            public BasePlayer player => _player ?? (_player = RustCore.FindPlayerById(userid));

            public bool IsParticipant
            {
                get
                {
                    return IsRaider || LockedOnEnter;
                }
                set
                {
                    IsRaider = value;
                    LockedOnEnter = value;
                }
            }
            public Raider(ulong userid, string username)
            {
                this.userid = userid;
                id = userid.ToString();
                displayName = username;
            }
            public Raider(BasePlayer target)
            {
                _player = target;
                userid = target.userID;
                id = target.UserIDString;
                displayName = target.displayName;
            }
            public void DestroyInput()
            {
                if (Input != null)
                {
                    UnityEngine.Object.Destroy(Input);
                }
            }
            public void Reset()
            {
                DestroyInput();
                IsAllowed = false;
                IsParticipant = false;
            }
        }

        public class RaidableBase : FacepunchBehaviour
        {
            private const float Radius = M_RADIUS;
            public HashSet<ulong> intruders { get; set; } = Pool.Get<HashSet<ulong>>();
            public Dictionary<ulong, Raider> raiders { get; set; } = Pool.Get<Dictionary<ulong, Raider>>();
            public Dictionary<ItemId, float> conditions { get; set; } = Pool.Get<Dictionary<ItemId, float>>();
            internal HashSet<StorageContainer> _containers { get; set; } = new HashSet<StorageContainer>();
            internal HashSet<StorageContainer> _allcontainers { get; set; } = new HashSet<StorageContainer>();
            public List<ScientistNPC> npcs { get; set; } = Pool.GetList<ScientistNPC>();
            public List<HotAirBalloon> habs { get; set; } = Pool.GetList<HotAirBalloon>();
            public List<BaseMountable> mountables { get; set; } = Pool.GetList<BaseMountable>();
            public Dictionary<NetworkableId, BackpackData> backpacks { get; set; } = Pool.Get<Dictionary<NetworkableId, BackpackData>>();
            public List<Vector3> foundations { get; set; } = new List<Vector3>();
            public List<Vector3> floors { get; set; } = new List<Vector3>();
            public List<BaseEntity> locks { get; set; } = Pool.GetList<BaseEntity>();
            private List<SphereEntity> spheres { get; set; } = Pool.GetList<SphereEntity>();
            private List<IOEntity> lights { get; set; } = Pool.GetList<IOEntity>();
            private List<BaseOven> ovens { get; set; } = Pool.GetList<BaseOven>();
            public List<AutoTurret> turrets { get; set; } = Pool.GetList<AutoTurret>();
            private List<Door> doors { get; set; } = Pool.GetList<Door>();
            private List<CustomDoorManipulator> doorControllers { get; set; } = Pool.GetList<CustomDoorManipulator>();
            private List<Locker> lockers { get; set; } = Pool.GetList<Locker>();
            private Dictionary<string, ulong> skins { get; set; } = Pool.Get<Dictionary<string, ulong>>();
            private Dictionary<uint, ulong> skinIds { get; set; } = Pool.Get<Dictionary<uint, ulong>>();
            private Dictionary<TriggerBase, BaseEntity> triggers { get; set; } = Pool.Get<Dictionary<TriggerBase, BaseEntity>>();
            private Dictionary<SleepingBag, ulong> _bags { get; set; } = Pool.Get<Dictionary<SleepingBag, ulong>>();
            public List<SamSite> samsites { get; set; } = Pool.GetList<SamSite>();
            public List<VendingMachine> vms { get; set; } = Pool.GetList<VendingMachine>();
            public Dictionary<string, ItemDefinition> Definitions { get; set; }
            public BuildingPrivlidge priv { get; set; }
            private Dictionary<string, List<string>> npcKits { get; set; }
            private MapMarkerExplosion explosionMarker { get; set; }
            private MapMarkerGenericRadius genericMarker { get; set; }
            private VendingMachineMapMarker vendingMarker { get; set; }
            public Coroutine setupRoutine { get; set; } = null;
            public Coroutine turretsCoroutine { get; set; } = null;
            private GameObject go { get; set; }
            private bool IsPrivDestroyed { get; set; }
            public bool IsDespawning { get; set; }
            public Vector3 Location { get; set; }
            public string ProfileName { get; set; }
            public string BaseName { get; set; }
            public bool ownerFlag { get; set; }
            public ulong permOwnerId { get; set; }
            public ulong ownerId { get; set; }
            public string ownerName { get; set; }
            public Raider riOwner { get; set; }
            public float loadTime { get; set; }
            public float spawnTime { get; set; }
            private DateTime spawnDateTime { get; set; }
            private Timer despawnTimer { get; set; }
            public float despawnTime { get; set; }
            private DateTime despawnDateTime { get; set; }
            public float AddNearTime { get; set; }
            public bool AllowPVP { get; set; }
            public BuildingOptions Options { get; set; }
            public bool IsAuthed { get; set; }
            public bool IsOpened { get; set; } = true;
            public bool IsResetting { get; set; }
            public bool IsUnloading { get; set; }
            public int npcMaxAmountMurderers { get; set; }
            public int npcMaxAmountScientists { get; set; }
            public int npcAmountThrown { get; set; }
            private bool isInvokingRespawnNpc { get; set; }
            public RaidableType Type { get; set; }
            public bool IsLoading { get; set; }
            private bool markerCreated { get; set; }
            private bool lightsOn { get; set; }
            private int itemAmountSpawned { get; set; }
            private int treasureAmount { get; set; }
            public bool privSpawned { get; set; }
            public string markerName { get; set; }
            public bool isAuthorized { get; set; }
            public bool IsEngaged { get; set; }
            public int _undoLimit { get; set; }
            private Dictionary<Elevator, BMGELEVATOR> Elevators { get; set; } = new Dictionary<Elevator, BMGELEVATOR>();
            private ItemDefinition lowgradefuel { get; set; } = ItemManager.FindItemDefinition("lowgradefuel");
            public HashSet<BaseEntity> Entities { get; set; } = new HashSet<BaseEntity>();
            public Dictionary<BaseEntity, Vector3> BuiltList { get; set; } = new Dictionary<BaseEntity, Vector3>();
            public RaidableSpawns spawns { get; set; }
            public float RemoveNearDistance { get; set; }
            public bool IsAnyLooted { get; set; }
            public bool IsDamaged { get; set; }
            public bool IsEligible { get; set; } = true;
            public bool IsCompleted { get; set; }
            private static bool isSpawnerBusy { get; set; }
            private static float isSpawnerBusyTime { get; set; }
            public float ProtectionRadius => Options.ProtectionRadius(Type);
            public int foundationsDestroyed { get; set; }
            public RaidableBases MyInstance { get; set; }
            public bool IsShuttingDown { get; set; }
            public bool stability { get; set; }

            private object[] hookObjects
            {
                get
                {
                    return new object[] { Location, 512, AllowPVP, null, spawnTime, despawnTime, loadTime, ownerId, GetOwner(), GetRaiders(), GetIntruders(), Entities.ToList(), BaseName, spawnDateTime, despawnDateTime, ProtectionRadius };
                }
            }

            public static bool IsSpawnerBusy
            {
                get
                {
                    if (!IsInstanceValid)
                    {
                        return true;
                    }

                    if (Time.time - isSpawnerBusyTime > 180f)
                    {
                        isSpawnerBusy = false;
                    }

                    return isSpawnerBusy;
                }
                set
                {
                    isSpawnerBusyTime = Time.time;
                    isSpawnerBusy = value;
                }
            }

            public Raider GetRaider(BasePlayer player)
            {
                Raider ri;
                if (!raiders.TryGetValue(player.userID, out ri))
                {
                    raiders[player.userID] = ri = new Raider(player);
                }
                return ri;
            }

            public bool CanHurtBox(BaseEntity entity)
            {
                if (Options.InvulnerableUntilCupboardIsDestroyed && IsBox(entity, false) && !priv.IsKilled()) return false;
                if (Options.Invulnerable && IsBox(entity, false)) return false;
                return true;
            }

            public void AddEntity(BaseEntity entity)
            {
                if (!entity.IsValid())
                {
                    return;
                }
                if (!MyInstance.temporaryData.NID.Contains(entity.net.ID.Value))
                {
                    MyInstance.temporaryData.NID.Add(entity.net.ID.Value);
                }
                Entities.Add(entity);
            }

            public void ResetToPool()
            {
                Interface.CallHook("OnRaidableBaseEnded", hookObjects);

                intruders.ResetToPool();
                raiders.ResetToPool();
                conditions.ResetToPool();
                backpacks.ResetToPool();
                locks.ResetToPool();
                npcs.ResetToPool();
                spheres.ResetToPool();
                lights.ResetToPool();
                ovens.ResetToPool();
                turrets.ResetToPool();
                doors.ResetToPool();
                doorControllers.ResetToPool();
                lockers.ResetToPool();
                skins.ResetToPool();
                skinIds.ResetToPool();
                triggers.ResetToPool();
                _bags.ResetToPool();
                samsites.ResetToPool();
                vms.ResetToPool();
                mountables.ResetToPool();
                habs.ResetToPool();
            }

            private void Awake()
            {
                markerName = config.Settings.Markers.MarkerName;
                spawnTime = Time.time;
                spawnDateTime = DateTime.Now;
                go = gameObject;
            }

            private void OnDestroy()
            {
                Despawn();
            }

            internal HashSet<BasePlayer> playersInSphere = new HashSet<BasePlayer>();
            internal HashSet<HotAirBalloon> habsInSphere = new HashSet<HotAirBalloon>();
            internal HashSet<BaseMountable> mountablesInSphere = new HashSet<BaseMountable>();
            internal List<BaseCombatEntity> checkEntities = new List<BaseCombatEntity>();
            internal float lastMountCheckTime;

            internal void CheckEntitiesInSphere()
            {
                if (IsUnloading)
                {
                    return;
                }
                FindEntities(Location, ProtectionRadius, 163848);
                CheckMountablesExiting();
                CheckMountablesEntering();
                CheckIntrudersExiting();
                CheckIntrudersEntering();
                habsInSphere.Clear();
                playersInSphere.Clear();
                mountablesInSphere.Clear();
            }

            public void FindEntities(Vector3 a, float n, int m)
            {
                checkEntities = FindEntitiesOfType<BaseCombatEntity>(a, n, m);
                for (int i = 0; i < checkEntities.Count; i++)
                {
                    var entity = checkEntities[i];
                    if (entity.IsKilled() || entity.IsNpc || entity.Health() <= 0f || entity.IsDead())
                    {
                        continue;
                    }
                    if (entity is BasePlayer)
                    {
                        playersInSphere.Add(entity as BasePlayer);
                    }
                    else if (entity is BaseMountable)
                    {
                        mountablesInSphere.Add(entity as BaseMountable);
                    }
                    else if (entity is HotAirBalloon)
                    {
                        habsInSphere.Add(entity as HotAirBalloon);
                    }
                }
            }

            private void CheckMountablesExiting()
            {
                if (habs.Count > 0 && Time.time > lastMountCheckTime)
                {
                    lastMountCheckTime = Time.time + 1f;
                    habs.RemoveAll(m => m.IsKilled() || m.health <= 0 || m.IsDead() || !habsInSphere.Contains(m));
                }
                if (mountables.Count > 0 && Time.time > lastMountCheckTime)
                {
                    lastMountCheckTime = Time.time + 1f;
                    mountables.RemoveAll(m => m.IsKilled() || m.health <= 0 || m.IsDead() || !mountablesInSphere.Contains(m));
                }
            }

            private void CheckMountablesEntering()
            {
                if (habsInSphere.Count > 0)
                {
                    habsInSphere.ForEach(m =>
                    {
                        if (!habs.Contains(m))
                        {
                            var players = GetMountedPlayers(m);

                            if (TryRemoveMountable(m, players))
                            {
                                playersInSphere.RemoveWhere(players.Contains);
                            }
                            else habs.Add(m);
                        }
                    });
                }
                if (mountablesInSphere.Count > 0)
                {
                    mountablesInSphere.ForEach(m =>
                    {
                        if (!mountables.Contains(m))
                        {
                            var players = GetMountedPlayers(m);
                            if (TryRemoveMountable(m, players))
                            {
                                playersInSphere.RemoveWhere(players.Contains);
                            }
                            else mountables.Add(m);
                        }
                    });
                }
            }

            private void CheckIntrudersExiting()
            {
                if (intruders.Count > 0)
                {
                    raiders.Values.ForEach(ri =>
                    {
                        if (!ri.player.IsNull() && !playersInSphere.Contains(ri.player) && intruders.Contains(ri.userid))
                        {
                            OnPlayerExit(ri.player, ri.player.IsDead());
                        }
                    });
                }
            }

            private void CheckIntrudersEntering()
            {
                if (playersInSphere.Count > 0)
                {
                    playersInSphere.ForEach(OnPreEnterRaid);
                }
            }

            private void OnPreEnterRaid(BasePlayer player)
            {
                if (player.IsNull() || intruders.Contains(player.userID) || !player.IsHuman() || player.IsDead() || IsUnderground(player.transform.position))
                {
                    return;
                }

                if (IsLoading && !CanBypass(player))
                {
                    RemovePlayer(player, Location, ProtectionRadius, Type);
                    return;
                }

                if (RemoveFauxAdmin(player) || IsScavenging(player))
                {
                    return;
                }

                OnEnterRaid(player, false);
            }

            public void OnEnterRaid(BasePlayer target, bool checkUnderground = true)
            {
                if (checkUnderground && IsUnderground(target.transform.position) || !target.IsConnected || target.IsDead())
                {
                    intruders.Remove(target.userID);
                    return;
                }

                if (CannotEnter(target, true))
                {
                    return;
                }

                if (!intruders.Add(target.userID))
                {
                    return;
                }

                Protector();

                if (!intruders.Contains(target.userID))
                {
                    return;
                }

                Raider ri = GetRaider(target);

                ri.DestroyInput();

                target.gameObject.AddComponent<PlayerInputEx>().Setup(this);

                StopUsingWeapon(target);

                if (config.EventMessages.AnnounceEnterExit)
                {
                    QueueNotification(target, AllowPVP ? "OnPlayerEntered" : "OnPlayerEnteredPVE");
                }

                UI.UpdateStatusUI(target);

                Interface.CallHook("OnPlayerEnteredRaidableBase", new object[] { target, Location, AllowPVP, 512, null, spawnTime, despawnTime, loadTime, ownerId, BaseName, spawnDateTime, despawnDateTime });

                if (config.Settings.Management.PVPDelay > 0)
                {
                    Interface.CallHook("OnPlayerPvpDelayEntry", new object[] { target, 512, Location, AllowPVP, null, spawnTime, despawnTime, loadTime, ownerId, BaseName, spawnDateTime, despawnDateTime });
                }

                foreach (var brain in MyInstance.HumanoidBrains.Values)
                {
                    if (InRange2D(brain.DestinationOverride, Location, brain.SenseRange))
                    {
                        brain.SwitchToState(AIState.Attack, -1);
                    }
                }

                ri.PreEnter = false;
            }

            public void OnPlayerExit(BasePlayer target, bool skipDelay = true)
            {
                if (target == null || !target.IsHuman() || !IsInstanceValid)
                {
                    return;
                }

                Raider ri = GetRaider(target);

                ri.DestroyInput();
                UI.DestroyStatusUI(target);

                if (!intruders.Remove(target.userID) || ri.PreEnter)
                {
                    return;
                }

                Interface.CallHook("OnPlayerExitedRaidableBase", new object[] { target, Location, AllowPVP, 512, null, spawnTime, despawnTime, loadTime, ownerId, BaseName, spawnDateTime, despawnDateTime });

                if (config.Settings.Management.PVPDelay > 0)
                {
                    if (skipDelay || !Instance.IsPVE() || !AllowPVP || target.IsFlying || target.limitNetworking)
                    {
                        goto enterExit;
                    }

                    if (config.EventMessages.AnnounceEnterExit)
                    {
                        string arg = mx("PVPFlag", target.UserIDString).Replace("[", string.Empty).Replace("] ", string.Empty);
                        QueueNotification(target, "DoomAndGloom", arg, config.Settings.Management.PVPDelay);
                    }

                    ulong id = target.userID;
                    DelaySettings ds;
                    if (!Instance.PvpDelay.TryGetValue(id, out ds))
                    {
                        Instance.PvpDelay[id] = ds = new DelaySettings
                        {
                            Timer = MyInstance.timer.Once(config.Settings.Management.PVPDelay, () =>
                            {
                                Interface.CallHook("OnPlayerPvpDelayExpired", new object[] { target, 512, Location, AllowPVP, null, spawnTime, despawnTime, loadTime, ownerId, BaseName, spawnDateTime, despawnDateTime });
                                Instance.PvpDelay.Remove(id);
                            }),
                            AllowPVP = AllowPVP,
                            RaidableBase = this,
                            time = config.Settings.Management.PVPDelay
                        };

                        UI.UpdateDelayUI(target);
                    }
                    else
                    {
                        ds.Timer.Reset();
                        ds.time = config.Settings.Management.PVPDelay;
                    }

                    return;
                }

            enterExit:
                if (config.EventMessages.AnnounceEnterExit)
                {
                    QueueNotification(target, AllowPVP ? "OnPlayerExit" : "OnPlayerExitPVE");
                }
            }

            private bool IsScavenging(BasePlayer player)
            {
                if (IsOpened || !config.Settings.Management.EjectScavengers || !ownerId.IsSteamId() || CanBypass(player))
                {
                    return false;
                }

                return !Any(player.userID) && !IsAlly(player) && RemovePlayer(player, Location, ProtectionRadius, Type);
            }

            private bool RemoveFauxAdmin(BasePlayer player)
            {
                if (player.IsReallyValid() && player.IsDeveloper && player.HasPermission("fauxadmin.allowed") && player.HasPermission("raidablebases.block.fauxadmin") && player.IsCheating())
                {
                    RemovePlayer(player, Location, ProtectionRadius, Type);
                    QueueNotification(player, "NoFauxAdmin");
                    OnPlayerExit(player, false);
                    return true;
                }

                return false;
            }

            private bool IsBanned(BasePlayer player)
            {
                if (player.HasPermission("raidablebases.banned"))
                {
                    QueueNotification(player, player.IsAdmin ? "BannedAdmin" : "Banned");
                    return true;
                }

                return false;
            }

            private bool Teleported(BasePlayer player)
            {
                if (!config.Settings.Management.AllowTeleport && player.IsConnected && !CanBypass(player) && NearFoundation(player.transform.position) && Interface.CallHook("OnBlockRaidableBasesTeleport", player, Location) == null)
                {
                    TryMessage(player, "CannotTeleport");
                    return true;
                }

                return false;
            }

            private bool IsHogging(BasePlayer player)
            {
                if (!config.Settings.Management.PreventHogging || !player.IsReallyValid() || CanBypass(player) || player.HasPermission("raidablebases.hoggingbypass"))
                {
                    return false;
                }

                foreach (var raid in Instance.Raids)
                {
                    if (raid.AllowPVP && config.Settings.Management.BypassUseOwnersForPVP)
                    {
                        continue;
                    }

                    if (!raid.AllowPVP && config.Settings.Management.BypassUseOwnersForPVE)
                    {
                        continue;
                    }

                    if (raid.IsOpened && raid.Location != Location && raid.Any(player.userID, false))
                    {
                        QueueNotification(player, "HoggingFinishYourRaid", PositionToGrid(raid.Location));
                        return true;
                    }
                }

                if (!config.Settings.Management.IsBlocking() || player.HasPermission("raidablebases.blockbypass"))
                {
                    return false;
                }

                return IsAllyHogging(player);
            }

            public bool IsAllyHogging(BasePlayer player, bool m = true)
            {
                foreach (var raid in Instance.Raids)
                {
                    if (raid.Location != Location && raid.IsOpened && IsAllyHogging(player, raid))
                    {
                        if (m)
                        {
                            QueueNotification(player, "HoggingFinishYourRaid", PositionToGrid(raid.Location));
                        }

                        return true;
                    }
                }

                return false;
            }

            private bool IsAllyHogging(BasePlayer player, RaidableBase raid)
            {
                if (CanBypass(player))
                {
                    return false;
                }

                if (raid.AllowPVP && config.Settings.Management.BypassUseOwnersForPVP)
                {
                    return false;
                }

                if (!raid.AllowPVP && config.Settings.Management.BypassUseOwnersForPVE)
                {
                    return false;
                }

                foreach (var target in raid.GetIntruders().Where(x => x != player && !CanBypass(x)))
                {
                    if (config.Settings.Management.BlockTeams && raid.IsAlly(player.userID, target.userID, AlliedType.Team))
                    {
                        TryMessage(player, "HoggingFinishYourRaidTeam", target.displayName, PositionToGrid(raid.Location));
                        return true;
                    }

                    if (config.Settings.Management.BlockFriends && raid.IsAlly(player.userID, target.userID, AlliedType.Friend))
                    {
                        TryMessage(player, "HoggingFinishYourRaidFriend", target.displayName, PositionToGrid(raid.Location));
                        return true;
                    }

                    if (config.Settings.Management.BlockClans && raid.IsAlly(player.userID, target.userID, AlliedType.Clan))
                    {
                        TryMessage(player, "HoggingFinishYourRaidClan", target.displayName, PositionToGrid(raid.Location));
                        return true;
                    }
                }

                return false;
            }

            private void CheckBackpacks(bool bypass = false)
            {
                foreach (var data in backpacks.ToList())
                {
                    if (EjectBackpack(data.Key, data.Value, bypass))
                    {
                        backpacks.Remove(data.Key);
                    }
                }
            }

            private void Protector()
            {
                if (backpacks.Count > 0)
                {
                    CheckBackpacks(!AllowPVP && Options.EjectBackpacksPVE);
                }

                if (intruders.Count == 0)
                {
                    return;
                }

                foreach (var ri in raiders.Values.ToList())
                {
                    if (ri.player.IsNull() || RemoveFauxAdmin(ri.player) || !intruders.Contains(ri.userid))
                    {
                        continue;
                    }

                    if (IsBanned(ri.player))
                    {
                        ri.Reset();
                        UI.DestroyStatusUI(ri.player);
                        RemovePlayer(ri.player, Location, ProtectionRadius, Type);
                        continue;
                    }

                    if (config.Settings.Management.Mounts.Jetpacks && IsWearingJetpack(ri.player))
                    {
                        RemovePlayer(ri.player, Location, ProtectionRadius, Type, true);
                        continue;
                    }

                    if (ri.player.userID == ownerId || ri.IsAllowed || CanBypass(ri.player))
                    {
                        continue;
                    }

                    if (CanEject(ri.player))
                    {
                        ri.Reset();
                        UI.DestroyStatusUI(ri.player);
                        RemovePlayer(ri.player, Location, ProtectionRadius, Type);
                        continue;
                    }

                    if (config.Settings.Management.LockToRaidOnEnter && !ri.LockedOnEnter)
                    {
                        QueueNotification(ri.player, "OnLockedToRaid");

                        ri.LockedOnEnter = true;
                    }

                    ri.IsAllowed = true;
                }
            }

            public void DestroyUI()
            {
                TryInvokeMethod(DestroyElevators);
                GetIntruders().ForEach(UI.DestroyStatusUI);
            }

            public void StopSetupCoroutine()
            {
                if (setupRoutine != null)
                {
                    StopCoroutine(setupRoutine);
                    setupRoutine = null;
                }
                if (turretsCoroutine != null)
                {
                    StopCoroutine(turretsCoroutine);
                    turretsCoroutine = null;
                }
            }

            public void Despawn()
            {
                if (!IsDespawning)
                {
                    IsDespawning = true;
                    TryInvokeMethod(LogDespawn);
                    TryInvokeMethod(RemoveAllFromEvent);
                    TryInvokeMethod(StopSetupCoroutine);
                    TryInvokeMethod(CancelInvokes);
                    TryInvokeMethod(SetNoDrops);
                    TryInvokeMethod(DestroyUI);
                    TryInvokeMethod(DestroyLocks);
                    TryInvokeMethod(DestroyNpcs);
                    TryInvokeMethod(DestroyInputs);
                    TryInvokeMethod(DestroySpheres);
                    TryInvokeMethod(DestroyElevators);
                    TryInvokeMethod(DestroyMapMarkers);
                    TryInvokeMethod(ResetSleepingBags);
                    TryInvokeMethod(CheckSubscribe);
                    TryInvokeMethod(ResetToPool);
                    if (!IsShuttingDown)
                    {
                        TryInvokeMethod(DestroyElevators);
                        TryInvokeMethod(DestroyEntities);
                    }
                    Destroy(this);
                    Destroy(go);
                }
            }

            private void LogDespawn()
            {
                MyInstance.LogToFile("despawn", $"{BaseName} {ownerName ?? "N/A"} ({ownerId}) @ {PositionToGrid(Location)} {Location}", MyInstance, true);
            }

            public void RemoveAllFromEvent()
            {
                IsOpened = false;

                Interface.CallHook("OnRaidableBaseDespawn", hookObjects);

                GetIntruders().ToList().ForEach(player => OnPlayerExit(player));
            }

            public void CheckSubscribe()
            {
                MyInstance.Raids.Remove(this);

                if (MyInstance.Raids.Count == 0)
                {
                    if (IsUnloading)
                    {
                        MyInstance.UnsetStatics();
                    }
                    else
                    {
                        MyInstance.UnsubscribeHooks();
                    }
                }

                if (!IsUnloading)
                {
                    spawns?.AddNear(Location, RemoveNearDistance, CacheType.Generic, AddNearTime);
                }
            }

            public void DestroyElevators()
            {
                if (Elevators?.Count > 0)
                {
                    TryInvokeMethod(RemoveParentFromEntitiesOnElevators);
                    Elevators.Keys.ToList().ForEach(SafelyKill);
                }
            }

            public void DestroyEntities()
            {
                if (!IsShuttingDown)
                {
                    MyInstance.UndoLoop(Entities.ToList(), _undoLimit, MyInstance.UndoMounts, MyInstance.UndoStructures, MyInstance.UndoDeployables, hookObjects);
                }
            }

            public void OnBuildingPrivilegeDestroyed()
            {
                Interface.CallHook("OnRaidableBasePrivilegeDestroyed", hookObjects);
                IsPrivDestroyed = true;
                TryToEnd();
            }

            public BasePlayer GetOwner()
            {
                BasePlayer owner = null;
                foreach (var x in raiders.Values)
                {
                    if (!x.player.IsReallyValid()) continue;
                    if (x.player.userID == ownerId) return x.player;
                    if (x.IsParticipant) owner = x.player;
                }
                return owner;
            }

            public List<BasePlayer> GetIntruders()
            {
                return raiders.Values.Where(x => intruders.Contains(x.userid) && x.player.IsReallyValid()).Select(x => x.player).ToList();
            }

            public List<BasePlayer> GetRaiders(bool participantOnly = true)
            {
                return raiders.Values.Where(x => x.player.IsReallyValid() && (!participantOnly || x.IsParticipant)).Select(x => x.player).ToList();
            }

            public bool AddLooter(BasePlayer looter, HitInfo hitInfo = null)
            {
                if (!looter.IsHuman())
                {
                    return false;
                }

                if (!IsAlly(looter))
                {
                    if (hitInfo != null)
                    {
                        if (CanEject())
                        {
                            NullifyDamage(hitInfo);
                        }
                        TryMessage(looter, "NoDamageToEnemyBase");
                    }
                    else
                    {
                        Message(looter, "OwnerLocked");
                    }
                    return false;
                }

                if (looter.IsFlying || looter.limitNetworking)
                {
                    return true;
                }

                if (IsHogging(looter))
                {
                    NullifyDamage(hitInfo);
                    return false;
                }

                GetRaider(looter).IsRaider = true;

                return true;
            }

            public bool IsBlacklisted(string name)
            {
                return Options.BlacklistedPickupItems.Exists(value => !string.IsNullOrEmpty(value) && name.Contains(value, CompareOptions.OrdinalIgnoreCase));
            }

            private void FillAmmoTurret(AutoTurret turret)
            {
                if (isAuthorized || IsUnloading || turret.IsKilled())
                {
                    return;
                }

                foreach (var id in turret.authorizedPlayers)
                {
                    if (id.userid.IsSteamId() && !CanBypassAuthorized(id.userid))
                    {
                        isAuthorized = true;
                        return;
                    }
                }

                var attachedWeapon = turret.GetAttachedWeapon();

                if (attachedWeapon.IsNull())
                {
                    turret.Invoke(() => FillAmmoTurret(turret), 0.2f);
                    return;
                }

                int p = Math.Max(config.Weapons.Ammo.AutoTurret, attachedWeapon.primaryMagazine.capacity);
                Item ammo = ItemManager.Create(attachedWeapon.primaryMagazine.ammoType, p, 0uL);
                if (!ammo.MoveToContainer(turret.inventory, -1, true, true, null, true)) ammo.Remove();
                attachedWeapon.primaryMagazine.contents = attachedWeapon.primaryMagazine.capacity;
                attachedWeapon.SendNetworkUpdateImmediate();
                turret.Invoke(turret.UpdateTotalAmmo, 0.25f);
            }

            private void FillAmmoGunTrap(GunTrap gt)
            {
                if (IsUnloading || isAuthorized || gt.IsKilled())
                {
                    return;
                }

                if (gt.ammoType == null)
                {
                    gt.ammoType = ItemManager.FindItemDefinition("ammo.handmade.shell");
                }

                var ammo = gt.inventory.GetSlot(0);

                if (ammo == null)
                {
                    gt.inventory.AddItem(gt.ammoType, config.Weapons.Ammo.GunTrap);
                }
                else ammo.amount = config.Weapons.Ammo.GunTrap;
            }

            private void FillAmmoFogMachine(FogMachine fm)
            {
                if (IsUnloading || isAuthorized || fm.IsKilled())
                {
                    return;
                }

                fm.inventory.AddItem(lowgradefuel, config.Weapons.Ammo.FogMachine);
            }

            private void FillAmmoFlameTurret(FlameTurret ft)
            {
                if (IsUnloading || isAuthorized || ft.IsKilled())
                {
                    return;
                }

                ft.inventory.AddItem(lowgradefuel, config.Weapons.Ammo.FlameTurret);
            }

            private void FillAmmoSamSite(SamSite ss)
            {
                if (IsUnloading || isAuthorized || ss.IsKilled())
                {
                    return;
                }

                if (ss.ammoItem == null || !ss.HasAmmo())
                {
                    Item item = ItemManager.Create(ss.ammoType, config.Weapons.Ammo.SamSite);

                    if (!item.MoveToContainer(ss.inventory))
                    {
                        item.Remove();
                    }
                    else ss.ammoItem = item;
                }
                else if (ss.ammoItem.amount < config.Weapons.Ammo.SamSite)
                {
                    ss.ammoItem.amount = config.Weapons.Ammo.SamSite;
                }
            }

            private void OnWeaponItemPreRemove(Item item)
            {
                if (isAuthorized || IsUnloading || IsDespawning)
                {
                    return;
                }
                else if (!priv.IsKilled() && priv.authorizedPlayers.Exists(id => id.userid.IsSteamId() && !CanBypassAuthorized(id.userid)))
                {
                    isAuthorized = true;
                    return;
                }
                else if (privSpawned && priv.IsKilled())
                {
                    isAuthorized = true;
                    return;
                }

                var weapon = item.parent?.entityOwner;

                if (weapon is AutoTurret)
                {
                    weapon.Invoke(() => FillAmmoTurret(weapon as AutoTurret), 0.1f);
                }
                else if (weapon is GunTrap)
                {
                    weapon.Invoke(() => FillAmmoGunTrap(weapon as GunTrap), 0.1f);
                }
                else if (weapon is SamSite)
                {
                    weapon.Invoke(() => FillAmmoSamSite(weapon as SamSite), 0.1f);
                }
            }

            private void OnItemAddedRemoved(Item item, bool bAdded)
            {
                if (!bAdded)
                {
                    TryToEnd();
                }
            }

            public void TryToEnd()
            {
                if (IsOpened && !IsLoading && CanUndo())
                {
                    UnlockEverything();
                    AwardRaiders();
                    Undo();
                }
            }

            private void UnlockEverything()
            {
                if (Options.UnlockEverything)
                {
                    DestroyLocks();
                }
            }

            public BasePlayer GetInitiatorPlayer(HitInfo hitInfo, BaseCombatEntity entity)
            {
                var weapon = hitInfo.Initiator ?? hitInfo.Weapon ?? hitInfo.WeaponPrefab;
                var attacker = weapon;

                if (weapon != null)
                {
                    if (!(attacker is BasePlayer) && weapon.creatorEntity is BasePlayer)
                    {
                        attacker = weapon.creatorEntity;
                    }

                    if (attacker == null)
                    {
                        attacker = weapon.HasParent() ? weapon.GetParentEntity() : weapon;
                    }
                }

                if (attacker == null && hitInfo.IsMajorityDamage(DamageType.Heat)) // workaround for game bug (ItemModProjectileSpawn.ServerProjectileHit) not setting baseEntity.creatorEntity = info.Initiator;
                {
                    attacker = entity.lastAttacker ?? GetArsonist();
                }

                return attacker as BasePlayer;
            }

            public BasePlayer GetArsonist()
            {
                foreach (var player in GetRaiders())
                {
                    if (player.svActiveItemID.Value == 0u) continue;
                    var item = player.GetActiveItem();
                    if (item == null) continue;
                    var name = item.info.displayName.english;
                    if (name.Contains("Incendiary")) return player;
                    if (name.Equals("Fire Arrow")) return player;
                }
                return null;
            }

            public void SetAllowPVP(RandomBase rb)
            {
                Type = rb.type;

                if (rb.type == RaidableType.Maintained && config.Settings.Maintained.Chance > 0)
                {
                    AllowPVP = Convert.ToDecimal(UnityEngine.Random.Range(0f, 100f)) <= config.Settings.Maintained.Chance;
                }
                else if (rb.type == RaidableType.Scheduled && config.Settings.Schedule.Chance > 0)
                {
                    AllowPVP = Convert.ToDecimal(UnityEngine.Random.Range(0f, 100f)) <= config.Settings.Schedule.Chance;
                }
                else if (rb.type == RaidableType.Maintained && config.Settings.Maintained.ConvertPVP)
                {
                    AllowPVP = false;
                }
                else if (rb.type == RaidableType.Scheduled && config.Settings.Schedule.ConvertPVP)
                {
                    AllowPVP = false;
                }
                else if (rb.type == RaidableType.Manual && config.Settings.Manual.ConvertPVP)
                {
                    AllowPVP = false;
                }
                else if (rb.type == RaidableType.Maintained && config.Settings.Maintained.ConvertPVE)
                {
                    AllowPVP = true;
                }
                else if (rb.type == RaidableType.Scheduled && config.Settings.Schedule.ConvertPVE)
                {
                    AllowPVP = true;
                }
                else if (rb.type == RaidableType.Manual && config.Settings.Manual.ConvertPVE)
                {
                    AllowPVP = true;
                }
                else AllowPVP = rb.Profile.Options.AllowPVP;
            }

            private bool CancelOnServerRestart()
            {
                return config.Settings.Management.Restart && IsShuttingDown;
            }

            public void AwardRaiders()
            {
                var sb = new StringBuilder();

                foreach (var ri in raiders.Values)
                {
                    if (ri.player.IsNull() || CancelOnServerRestart() || !IsEligible)
                    {
                        ri.reward = false;
                        continue;
                    }

                    if (ri.player.IsFlying)
                    {
                        if (config.EventMessages.Rewards.Flying) Message(ri.player, "No Reward: Flying");
                        ri.reward = false;
                        continue;
                    }

                    if (ri.player._limitedNetworking)
                    {
                        if (config.EventMessages.Rewards.Vanished) Message(ri.player, "No Reward: Vanished");
                        ri.reward = false;
                        continue;
                    }

                    if (!IsPlayerActive(ri.userid))
                    {
                        if (config.EventMessages.Rewards.Inactive) Message(ri.player, "No Reward: Inactive");
                        ri.reward = false;
                        continue;
                    }

                    if (config.Settings.RemoveAdminRaiders && ri.player.IsAdmin)
                    {
                        if (config.EventMessages.Rewards.RemoveAdmin) Message(ri.player, "No Reward: Admin");
                        ri.reward = false;
                        continue;
                    }

                    if (config.Settings.Management.OnlyAwardOwner && ri.player.userID != ownerId && ownerId.IsSteamId())
                    {
                        if (config.EventMessages.Rewards.NotOwner) Message(ri.player, "No Reward: Not Owner");
                        ri.reward = false;
                    }

                    if (!ri.IsParticipant)
                    {
                        if (config.EventMessages.Rewards.NotParticipant) Message(ri.player, "No Reward: Not A Participant");
                        ri.reward = false;
                        continue;
                    }

                    if (config.Settings.Management.OnlyAwardAllies && ri.player.userID != ownerId && !IsAlly(ri.userid, ownerId))
                    {
                        if (config.EventMessages.Rewards.NotAlly) Message(ri.player, "No Reward: Not Ally");
                        ri.reward = false;
                    }

                    sb.Append(ri.displayName).Append(", ");
                }

                if (IsEligible)
                {
                    if (!CancelOnServerRestart())
                    {
                        Interface.CallHook("OnRaidableBaseCompleted", hookObjects);
                    }

                    if (Options.Levels.Level2 && npcMaxAmountMurderers + npcMaxAmountScientists > 0)
                    {
                        SpawnNpcs();
                    }

                    if (IsCompleted)
                    {
                        HandleAwards();
                    }
                }

                if (sb.Length == 0)
                {
                    return;
                }

                sb.Length -= 2;
                string thieves = sb.ToString();
                string posStr = FormatGridReference(Location);
                string con = mx(IsEligible ? "Thieves" : "ThievesDespawn", null, mx("Normal"), posStr, thieves);

                Puts(con);

                if (config.EventMessages.AnnounceThief && IsEligible)
                {
                    foreach (var target in BasePlayer.activePlayerList)
                    {
                        string mode = mx("Normal", target.UserIDString);
                        QueueNotification(target, "Thieves", mode, posStr, thieves);
                    }
                }

                if (config.EventMessages.LogThieves)
                {
                    MyInstance.LogToFile("treasurehunters", $"{DateTime.Now} : {con}", MyInstance, false);
                }
            }

            private void HandleAwards()
            {
                foreach (var ri in raiders.Values)
                {
                    if (!ri.IsParticipant || !ri.reward)
                    {
                        continue;
                    }

                    if (config.RankedLadder.Enabled)
                    {
                        PlayerInfo playerInfo = PlayerInfo.Get(ri.id);

                        playerInfo.ResetExpiredDate();

                        playerInfo.TotalRaids++;
                        playerInfo.Raids++;

                        Interface.CallHook("OnRaidableAwardGiven", ri.displayName, ri.id, JsonConvert.SerializeObject(playerInfo));
                    }

                    int total = raiders.Values.ToList().Sum(x => x.IsParticipant ? 1 : 0);

                    if (Options.Rewards.Money > 0)
                    {
                        double money = config.Settings.Management.DivideRewards ? Options.Rewards.Money / total : Options.Rewards.Money;
                        if (Convert.ToBoolean(Instance.Economics?.Call("Deposit", ri.id, money)))
                        {
                            QueueNotification(ri.player, "EconomicsDeposit", money);
                        }
                    }

                    if (Options.Rewards.Money > 0 && Instance.IQEconomic.CanCall())
                    {
                        int money = Convert.ToInt32(config.Settings.Management.DivideRewards ? Options.Rewards.Money / total : Options.Rewards.Money);
                        Instance.IQEconomic?.Call("API_SET_BALANCE", ri.userid, money);
                        QueueNotification(ri.player, "EconomicsDeposit", money);
                    }

                    if (Options.Rewards.Points > 0 && Instance.ServerRewards.CanCall())
                    {
                        int points = config.Settings.Management.DivideRewards ? Options.Rewards.Points / total : Options.Rewards.Points;
                        Instance.ServerRewards?.Call("AddPoints", ri.userid, points);
                        QueueNotification(ri.player, "ServerRewardPoints", points);
                    }

                    if (Options.Rewards.XP > 0 && Instance.SkillTree.CanCall())
                    {
                        double xp = config.Settings.Management.DivideRewards ? Options.Rewards.XP / total : Options.Rewards.XP;
                        QueueNotification(ri.player, "SkillTreeXP", xp);
                        Instance.SkillTree?.Call("AwardXP", ri.player, xp);
                    }
                }
            }

            private bool CanAssignTo(ulong id, bool value)
            {
                return value == false || ownerId == 0uL || id == ownerId;
            }

            private List<string> messagesSent = new List<string>();

            public bool TryMessage(BasePlayer player, string key, params object[] args)
            {
                if (player.IsNull() || messagesSent.Contains(player.UserIDString))
                {
                    return false;
                }

                string userid = player.UserIDString;

                messagesSent.Add(userid);
                MyInstance.timer.Once(10f, () => messagesSent.Remove(userid));
                Message(player, key, args);

                return true;
            }

            public bool CanBypass(BasePlayer player)
            {
                return !player.IsHuman() || player.IsFlying || player.limitNetworking || player.HasPermission("raidablebases.canbypass");
            }

            private bool Exceeds(BasePlayer player)
            {
                if (CanBypass(player) || config.Settings.Management.Players.BypassPVP && AllowPVP)
                {
                    return false;
                }

                int amount = config.Settings.Management.Players.Get(Type);

                if (amount == 0)
                {
                    return false;
                }

                return amount == -1 || intruders.Count >= amount;
            }

            public string Mode(string userid = null, bool forceShowName = false)
            {
                var difficultyMode = mx("Normal");

                if (difficultyMode == "normal")
                {
                    difficultyMode = "Normal";
                }

                if (ownerId.IsSteamId())
                {
                    return string.Format("{0} {1}", (config.Settings.Markers.ShowOwnersName || forceShowName) ? ownerName : mx("Claimed"), difficultyMode);
                }

                return difficultyMode;
            }

            private void SetOwnerInternal(BasePlayer player)
            {
                if (config.Settings.Management.LockTime > 0f)
                {
                    if (IsInvoking(ResetOwner)) CancelInvoke(ResetOwner);
                    Invoke(ResetOwner, config.Settings.Management.LockTime * 60f);
                }
                riOwner = GetRaider(player);
                ownerId = player.userID;
                ownerName = player.displayName;
                permOwnerId = ownerId;
                riOwner.IsAlly = true;
                riOwner.IsAllowed = true;
                UpdateMarker();
            }

            private bool IsPlayerActive(ulong userid)
            {
                if (config.Settings.Management.LockTime <= 0f)
                {
                    return true;
                }

                Raider raider;
                if (!raiders.TryGetValue(userid, out raider))
                {
                    return true;
                }

                return (config.Settings.Management.LockTime * 60f) - (Time.time - raider.lastActiveTime) > 0;
            }

            public void TrySetOwner(BasePlayer attacker, BaseEntity entity, HitInfo hitInfo)
            {
                if (!config.Settings.Management.UseOwners || !IsOpened || ownerId.IsSteamId() || config.Settings.Management.PreventHogging && IsOwner(attacker, false))
                {
                    return;
                }

                if (config.Settings.Management.BypassUseOwnersForPVP && AllowPVP || config.Settings.Management.BypassUseOwnersForPVE && !AllowPVP)
                {
                    return;
                }

                if (IsHogging(attacker))
                {
                    NullifyDamage(hitInfo);
                    return;
                }

                if (entity is ScientistNPC)
                {
                    SetOwner(attacker);
                    return;
                }

                if (!(entity is BuildingBlock) && !(entity is Door) && !(entity is SimpleBuildingBlock))
                {
                    return;
                }

                if (InRange2D(attacker.transform.position, Location, ProtectionRadius) || IsLootingWeapon(hitInfo))
                {
                    SetOwner(attacker);
                }
            }

            public bool SetOwner(BasePlayer player)
            {
                SetOwnerInternal(player);
                ResetRaiderRelations();
                Protector();
                return true;
            }

            public void ResetRaiderRelations()
            {
                foreach (var ri in raiders.Values.ToList())
                {
                    if (ri.userid == ownerId)
                    {
                        continue;
                    }

                    ri.IsAllowed = false;
                    ri.IsAlly = false;
                }
            }

            public void ClearEnemies()
            {
                raiders.RemoveAll((uid, ri) => !ri.player.IsReallyConnected() || !IsAlly(ri.player));
            }

            public void CheckDespawn()
            {
                if (!IsOpened)
                {
                    TryResetDespawn();
                    return;
                }

                if (IsDespawning || config.Settings.Management.DespawnMinutesInactive <= 0 || config.Settings.Management.Engaged && !IsEngaged)
                {
                    return;
                }

                if (IsInvoking(Despawn))
                {
                    CancelInvoke(Despawn);
                }

                if (!config.Settings.Management.DespawnMinutesInactiveReset && despawnTime != 0)
                {
                    return;
                }

                float time = config.Settings.Management.DespawnMinutesInactive * 60f;
                despawnTime = Time.time + time;
                despawnDateTime = DateTime.Now.AddSeconds(time);
                Invoke(Despawn, time);
            }

            private void TryResetDespawn()
            {
                if (config.Settings.Management.DespawnMinutesReset && despawnTimer != null)
                {
                    float time = config.Settings.Management.DespawnMinutes * 60f;
                    despawnTime = Time.time + time;
                    despawnDateTime = DateTime.Now.AddSeconds(time);
                    despawnTimer.Reset();
                    CancelInvoke(Despawn);
                    Invoke(Despawn, time);
                }
            }

            public bool EndWhenCupboardIsDestroyed()
            {
                if (config.Settings.Management.EndWhenCupboardIsDestroyed && privSpawned)
                {
                    return IsCompleted = IsPrivDestroyed || priv.IsKilled() || priv.inventory.IsEmpty();
                }

                return false;
            }

            public bool CanUndo()
            {
                if (EndWhenCupboardIsDestroyed())
                {
                    return true;
                }

                if (config.Settings.Management.RequireCupboardLooted && privSpawned && (ownerId == 0 || IsPlayerActive(ownerId)))
                {
                    if (!priv.IsKilled() && !priv.inventory.IsEmpty())
                    {
                        return false;
                    }
                }

                foreach (var container in _containers)
                {
                    if (!container.IsKilled() && !container.inventory.IsEmpty() && IsBox(container, true))
                    {
                        return false;
                    }
                }

                foreach (string value in config.Settings.Management.Inherit)
                {
                    foreach (var container in _allcontainers)
                    {
                        if (container.IsKilled() || !container.ShortPrefabName.Contains(value, CompareOptions.OrdinalIgnoreCase))
                        {
                            continue;
                        }

                        if (!container.inventory.IsEmpty())
                        {
                            return false;
                        }
                    }
                }

                return IsCompleted = true;
            }

            private bool CanPlayerBeLooted(ulong looter, ulong target)
            {
                if (!config.Settings.Management.PlayersLootableInPVE && !AllowPVP || !config.Settings.Management.PlayersLootableInPVP && AllowPVP)
                {
                    return IsAlly(looter, target);
                }

                return true;
            }

            private bool CanBeLooted(BasePlayer player, BaseEntity e)
            {
                if (IsLoading)
                {
                    return CanBypassAuthorized(player.userID);
                }

                if (IsProtectedWeapon(e, true))
                {
                    if (config.Settings.Management.LootableTraps && !CanBypassAuthorized(player.userID))
                    {
                        isAuthorized = true;
                        return true;
                    }

                    return false;
                }

                if (e is NPCPlayerCorpse)
                {
                    return true;
                }

                if (e is LootableCorpse)
                {
                    if (CanBypass(player))
                    {
                        return true;
                    }

                    var corpse = e as LootableCorpse;

                    if (!corpse.playerSteamID.IsSteamId() || corpse.playerSteamID == player.userID || corpse.playerName == player.displayName)
                    {
                        return true;
                    }

                    return CanPlayerBeLooted(player.userID, corpse.playerSteamID);
                }
                else if (e is DroppedItemContainer)
                {
                    if (CanBypass(player))
                    {
                        return true;
                    }

                    var container = e as DroppedItemContainer;

                    if (!container.playerSteamID.IsSteamId() || container.playerSteamID == player.userID || container.playerName == player.displayName)
                    {
                        return true;
                    }

                    return CanPlayerBeLooted(player.userID, container.playerSteamID);
                }

                return true;
            }

            public bool IsProtectedWeapon(BaseEntity e, bool checkBuiltList = false)
            {
                if (!e.IsReallyValid() || checkBuiltList && BuiltList.ContainsKey(e))
                {
                    return false;
                }

                return e is GunTrap || e is FlameTurret || e is FogMachine || e is SamSite || e is AutoTurret;
            }

            public object CanLootEntityInternal(BasePlayer player, BaseEntity entity)
            {
                if (!entity.OwnerID.IsSteamId() && !RaidableBase.Has(entity))
                {
                    return null;
                }

                if (entity.ShortPrefabName == "coffinstorage" && Mathf.Approximately(entity.transform.position.Distance(new Vector3(0f, -50f, 0f)), 0f))
                {
                    return null;
                }

                if (entity.OwnerID == player.userID || entity is BaseMountable)
                {
                    return null;
                }

                if (IsBlacklisted(entity.ShortPrefabName))
                {
                    return true;
                }

                if (entity.HasParent() && entity.GetParentEntity() is BaseMountable)
                {
                    return null;
                }

                if (!player.limitNetworking && !CanBeLooted(player, entity))
                {
                    return true;
                }

                if (entity is LootableCorpse || entity is DroppedItemContainer)
                {
                    return null;
                }

                if (player.GetMounted())
                {
                    Message(player, "CannotBeMounted");
                    return true;
                }

                if (Options.RequiresCupboardAccess && !CanBuild(player))
                {
                    Message(player, "MustBeAuthorized");
                    return true;
                }

                if (!IsAlly(player))
                {
                    Message(player, "OwnerLocked");
                    return true;
                }

                if (raiders.Exists(ri => ri.Value.IsParticipant))
                {
                    CheckDespawn();
                }

                return AddLooter(player) ? (object)null : true;
            }

            public bool CanBuild(BasePlayer player)
            {
                if (privSpawned)
                {
                    return priv.IsKilled() || priv.IsAuthed(player);
                }
                return true;
            }

            public static void ClearInventory(ItemContainer container)
            {
                if (container == null || container.itemList == null)
                {
                    return;
                }
                Item[] array = container.itemList.ToArray();
                for (int i = 0; i < array.Length; i++)
                {
                    array[i].GetHeldEntity().SafelyKill();
                    array[i].RemoveFromContainer();
                    array[i].Remove(0f);
                }
            }

            public void SetNoDrops()
            {
                foreach (var container in _allcontainers)
                {
                    if (container.IsKilled())
                    {
                        continue;
                    }
                    else if (!IsShuttingDown && IsCompleted && Options.DropPrivilegeLoot && container is BuildingPrivlidge)
                    {
                        DropOrRemoveItems(container, this);
                    }
                    else
                    {
                        container.dropsLoot = false;
                        ClearInventory(container.inventory);
                    }
                }

                foreach (var turret in turrets)
                {
                    if (!turret.IsKilled())
                    {
                        if (!IsShuttingDown)
                        {
                            Interface.Oxide.NextTick(turret.SafelyKill);
                        }
                        ClearInventory(turret.inventory);
                    }
                }

                ItemManager.DoRemoves();
            }

            public void DestroyInputs()
            {
                raiders.Values.ToList().ForEach(ri => ri.DestroyInput());
            }

            public void Init(RandomBase rb, List<BaseEntity> entities = null)
            {
                RemoveNearDistance = rb.spawns == null ? rb.Profile.Options.ProtectionRadius(rb.type) : rb.spawns.RemoveNear(rb.Position, rb.Profile.Options.ProtectionRadius(rb.type), CacheType.Generic, rb.type);

                Instance.Cycle.Add(rb.type, rb.BaseName);

                spawns = rb.spawns;
                Elevators = BMGELEVATOR.FixElevators(this);

                TryInvokeMethod(() => AddEntities(entities));

                Interface.Oxide.NextTick(() =>
                {
                    TryInvokeMethod(SetCenterFromMultiplePoints);
                    TryInvokeMethod(SetupElevators);

                    setupRoutine = ServerMgr.Instance.StartCoroutine(EntitySetup());
                });
            }

            private void SetupElevators()
            {
                if (Elevators == null || Elevators.Count == 0)
                {
                    return;
                }

                Elevators.ToList().ForEach(element => element.Value.Init(this));
            }

            private List<string> unityEngineScripts { get; set; } = new List<string> { "saddletest", "fuel_storage" };

            private void AddEntities(List<BaseEntity> entities)
            {
                if (entities.IsNullOrEmpty())
                {
                    return;
                }
                foreach (var e in entities.ToList())
                {
                    if (e.IsKilled())
                    {
                        entities.Remove(e);
                        continue;
                    }
                    if (unityEngineScripts.Contains(e.ShortPrefabName))
                    {
                        Interface.Oxide.NextTick(e.SafelyKill);
                        entities.Remove(e);
                        continue;
                    }
                    if (e.ShortPrefabName == "foundation.triangle" || e.ShortPrefabName == "foundation" || e.skinID == 1337424001 && e is CollectibleEntity)
                    {
                        foundations.Add(e.transform.position);
                    }
                    if (e.ShortPrefabName.StartsWith("floor"))
                    {
                        floors.Add(e.transform.position);
                    }
                    e.OwnerID = 0;
                    AddEntity(e);
                }
                MyInstance.SaveTemporaryData();
            }

            public void SetCenterFromMultiplePoints()
            {
                if (foundations.Count == 0)
                {
                    foundations.AddRange(floors);
                    floors = null;
                }

                if (foundations.Count < 2)
                {
                    return;
                }

                float x = 0f;
                float z = 0f;

                foreach (var position in foundations)
                {
                    x += position.x;
                    z += position.z;
                }

                var vector = new Vector3(x / foundations.Count, 0f, z / foundations.Count);

                if (Options.Setup.ForcedHeight != -1)
                {
                    vector.y = Options.Setup.ForcedHeight;
                }
                else vector.y = SpawnsController.GetSpawnHeight(vector);

                Location = vector;
            }

            private void CreateSpheres()
            {
                if (Options.SphereAmount <= 0 || Options.Silent)
                {
                    return;
                }

                for (int i = 0; i < Options.SphereAmount; i++)
                {
                    var sphere = GameManager.server.CreateEntity(StringPool.Get(3211242734), Location) as SphereEntity;

                    if (sphere.IsNull())
                    {
                        break;
                    }

                    sphere.currentRadius = 1f;
                    sphere.Spawn();
                    sphere.LerpRadiusTo(ProtectionRadius * 2f, ProtectionRadius * 0.75f);
                    spheres.Add(sphere);
                }
            }

            private void CreateZoneWalls()
            {
                if (!Options.ArenaWalls.Enabled)
                {
                    return;
                }

                var minHeight = 999f;
                var maxHeight = -999f;
                var maxDistance = 48f;
                var stacks = Options.ArenaWalls.Stacks;
                var center = new Vector3(Location.x, Location.y, Location.z);
                var gap = Options.ArenaWalls.Stone || Options.ArenaWalls.Ice ? 0.3f : 0.5f;
                var prefab = Options.ArenaWalls.Ice ? StringPool.Get(921229511) : Options.ArenaWalls.Stone ? StringPool.Get(1585379529) : StringPool.Get(1745077396);
                var next1 = Mathf.CeilToInt(360 / Options.ArenaWalls.Radius * 0.1375f);
                var next2 = 360 / Options.ArenaWalls.Radius - gap;

                foreach (var position in SpawnsController.GetCircumferencePositions(center, Options.ArenaWalls.Radius, next1, false, false, 1f))
                {
                    float y = SpawnsController.GetSpawnHeight(position, false, false, targetMask | Layers.Mask.Construction);
                    maxHeight = Mathf.Max(y, maxHeight, TerrainMeta.WaterMap.GetHeight(position));
                    minHeight = Mathf.Min(y, minHeight);
                    center.y = minHeight;
                }

                if (Options.Setup.ForcedHeight > 0)
                {
                    maxDistance += Options.Setup.ForcedHeight;
                    Options.ArenaWalls.Stone = true;
                    Options.ArenaWalls.Ice = false;
                    stacks = Mathf.CeilToInt(Options.Setup.ForcedHeight / 6f);
                }
                else if (Options.ArenaWalls.IgnoreWhenClippingTerrain)
                {
                    stacks += Mathf.CeilToInt((maxHeight - minHeight) / 6f);
                }

                for (int i = 0; i < stacks; i++)
                {
                    if (Options.Setup.ForcedHeight != -1f && i < stacks * 0.75)
                    {
                        center.y += 6f;
                        continue;
                    }

                    foreach (var position in SpawnsController.GetCircumferencePositions(center, Options.ArenaWalls.Radius, next2, false, false, center.y))
                    {
                        if ((Location - position).y > maxDistance)
                        {
                            continue;
                        }

                        float spawnHeight = TerrainMeta.HeightMap.GetHeight(new Vector3(position.x, position.y + 6f, position.z));

                        if (i == 0 && position.y + 8.018669f < spawnHeight)
                        {
                            continue;
                        }

                        if (spawnHeight > position.y + 6.5f)
                        {
                            continue;
                        }

                        if (Options.ArenaWalls.LeastAmount)
                        {
                            float h = SpawnsController.GetSpawnHeight(position, true, false, targetMask | Layers.Mask.Construction);
                            float j = stacks * 6f + 6f;

                            if (position.y - spawnHeight > j && position.y < h)
                            {
                                continue;
                            }
                        }

                        var e = GameManager.server.CreateEntity(prefab, position, Quaternion.identity, false);

                        if (e.IsNull())
                        {
                            return;
                        }

                        e.transform.LookAt(center, Vector3.up);

                        if (Options.ArenaWalls.UseUFOWalls)
                        {
                            e.transform.Rotate(-67.5f, 0f, 0f);
                        }

                        e.Spawn();
                        e.gameObject.SetActive(true);

                        SetupEntity(e);

                        if (Options.ArenaWalls.IgnoreWhenClippingTerrain && stacks == i - 1)
                        {
                            RaycastHit hit;
                            if (Physics.Raycast(new Vector3(position.x, position.y + 6.5f, position.z), Vector3.down, out hit, 13f, targetMask))
                            {
                                if (hit.collider.ObjectName().Contains("rock") || hit.collider.ObjectName().Contains("formation", CompareOptions.OrdinalIgnoreCase))
                                {
                                    stacks++;
                                }
                            }
                        }
                    }

                    center.y += 6f;
                }
            }

            private void RemoveClutter()
            {
                foreach (var e in FindEntitiesOfType<BaseEntity>(Location, ProtectionRadius))
                {
                    if (e is TreeEntity)
                    {
                        if (!Entities.Contains(e)) e.SafelyKill();
                    }
                    else if ((e is ResourceEntity || e is CollectibleEntity) && NearFoundation(e.transform.position))
                    {
                        e.SafelyKill();
                    }
                    else if (e is SleepingBag)
                    {
                        SleepingBagHandler(e as SleepingBag);
                    }
                    else if (e is HotAirBalloon && NearFoundation(e.transform.position, 10f) && !Entities.Contains(e))
                    {
                        TryEjectMountable(e);
                    }
                    else if (e is BaseMountable && NearFoundation(e.transform.position, 10f) && !(e.GetParentEntity() is TrainCar) && !Entities.Contains(e))
                    {
                        TryEjectMountable(e);
                    }
                    else if (e is ScientistNPC && NearFoundation(e.transform.position, 15f))
                    {
                        e.SafelyKill();
                    }
                }
            }

            private void SleepingBagHandler(SleepingBag bag)
            {
                if (!Entities.Contains(bag))
                {
                    _bags[bag] = bag.deployerUserID;

                    bag.deployerUserID = 0uL;
                    bag.unlockTime = UnityEngine.Time.realtimeSinceStartup + 99999f;
                }
            }

            public void ResetSleepingBags()
            {
                foreach (var element in _bags)
                {
                    if (element.Key.IsKilled()) continue;
                    element.Key.deployerUserID = element.Value;
                    element.Key.unlockTime = UnityEngine.Time.realtimeSinceStartup;
                }
            }

            private IEnumerator EntitySetup()
            {
                TryInvokeMethod(RemoveClutter);

                int checks = 0;
                float invokeTime = 0f;
                int limit = Mathf.Clamp(Options.Setup.SpawnLimit, 1, 500);

                foreach (var e in Entities.ToList())
                {
                    TryInvokeMethod(() => TrySetupEntity(e, ref invokeTime));

                    if (++checks >= limit)
                    {
                        checks = 0;
                        yield return CoroutineEx.waitForSeconds(0.025f);
                    }
                }

                yield return CoroutineEx.waitForSeconds(2f);

                if (SetupLoot())
                {
                    TryInvokeMethod(Subscribe);
                    TryInvokeMethod(SetupTurrets);
                    TryInvokeMethod(CreateGenericMarker);
                    TryInvokeMethod(UpdateMarker);
                    TryInvokeMethod(EjectSleepers);
                    TryInvokeMethod(CreateZoneWalls);
                    TryInvokeMethod(CreateSpheres);
                    TryInvokeMethod(SetupLights);
                    TryInvokeMethod(SetupDoorControllers);
                    TryInvokeMethod(SetupDoors);
                    TryInvokeMethod(CheckDespawn);
                    TryInvokeMethod(SetupContainers);
                    TryInvokeMethod(MakeAnnouncements);
                    InvokeRepeating(Protector, 1f, 1f);
                    Interface.CallHook("OnRaidableBaseStarted", hookObjects);
                }
                else
                {
                    Despawn();
                }

                loadTime = Time.time - loadTime;
                IsLoading = false;
                IsSpawnerBusy = false;
                setupRoutine = null;
            }

            private void TrySetupEntity(BaseEntity e, ref float invokeTime)
            {
                if (!CanSetupEntity(e))
                {
                    return;
                }
                
                SetupEntity(e);

                e.OwnerID = 0;

                if (e.skinID == 1337424001 && e is CollectibleEntity)
                {
                    (e as CollectibleEntity).itemList = null; // WaterBases compatibility
                }

                if (!Options.AllowPickup && e is BaseCombatEntity)
                {
                    SetupPickup(e as BaseCombatEntity);
                }

                if (e is IOEntity)
                {
                    if (e is ContainerIOEntity)
                    {
                        SetupIO(e as ContainerIOEntity);
                    }
                    else if (e is ElectricBattery)
                    {
                        SetupBattery(e as ElectricBattery);
                    }
                    if (e is AutoTurret)
                    {
                        var turret = e as AutoTurret;

                        triggers[turret.targetTrigger] = turret;

                        SetupTurret(turret);
                    }
                    else if (e is Igniter)
                    {
                        SetupIgniter(e as Igniter);
                    }
                    else if (e is SamSite)
                    {
                        SetupSamSite(e as SamSite);
                    }
                    else if (e is TeslaCoil)
                    {
                        SetupTeslaCoil(e as TeslaCoil);
                    }
                    else if (e.name.Contains("light"))
                    {
                        SetupLight(e as IOEntity);
                    }
                    else if (e is CustomDoorManipulator)
                    {
                        doorControllers.Add(e as CustomDoorManipulator);
                    }
                    else if (e is HBHFSensor)
                    {
                        SetupHBHFSensor(e as HBHFSensor);
                    }
                    else if (e.ShortPrefabName == "generator.small" || e.ShortPrefabName == "generator.static")
                    {
                        SetupGenerator(e as ElectricGenerator);
                    }
                    else if (e is PressButton)
                    {
                        SetupButton(e as PressButton);
                    }
                    else if (e is FogMachine)
                    {
                        SetupFogMachine(e as FogMachine);
                    }
                }
                else if (e is StorageContainer)
                {
                    SetupContainer(e as StorageContainer);

                    if (e is BaseOven)
                    {
                        ovens.Add(e as BaseOven);
                    }
                    else if (e is FlameTurret)
                    {
                        SetupFlameTurret(e as FlameTurret);
                    }
                    else if (e is VendingMachine)
                    {
                        SetupVendingMachine(e as VendingMachine);
                    }
                    else if (e is BuildingPrivlidge)
                    {
                        SetupBuildingPriviledge(e as BuildingPrivlidge);
                    }
                    else if (e is Locker)
                    {
                        SetupLocker(e as Locker);
                    }
                    else if (e is GunTrap)
                    {
                        SetupGunTrap(e as GunTrap);
                    }
                }
                else if (e is BuildingBlock)
                {
                    SetupBuildingBlock(e as BuildingBlock);
                }
                else if (e is BaseLock)
                {
                    SetupLock(e);
                }
                else if (e is SleepingBag)
                {
                    SetupSleepingBag(e as SleepingBag);
                }
                else if (e is BaseMountable)
                {
                    SetupMountable(e as BaseMountable);
                }
                else if (e is CollectibleEntity)
                {
                    SetupCollectible(e as CollectibleEntity);
                }
                else if (e is SpookySpeaker)
                {
                    SetupSpookySpeaker(e as SpookySpeaker);
                }

                if (e is DecayEntity)
                {
                    SetupDecayEntity(e as DecayEntity);
                }

                if (e is Door)
                {
                    var door = e as Door;

                    if (door.canTakeLock && !door.isSecurityDoor)
                    {
                        doors.Add(door);
                    }
                }
                else SetupSkin(e);
            }

            private void SetupLights()
            {
                if (Instance.NightLantern.CanCall())
                {
                    return;
                }

                if (config.Settings.Management.Lights || config.Settings.Management.AlwaysLights)
                {
                    ToggleLights();
                }
            }

            internal void SetupCollider()
            {
                try
                {
                    go.transform.position = Location;

                    InvokeRepeating(CheckEntitiesInSphere, 0.1f, 0.1f);
                }
                catch
                {
                    Invoke(SetupCollider, 0.1f);
                }
            }

            private bool SetupLoot()
            {
                _containers.RemoveWhere(x => x.IsKilled());

                treasureAmount = Options.MinTreasure > 0 ? UnityEngine.Random.Range(Options.MinTreasure, Options.MaxTreasure + 1) : Options.MaxTreasure;

                if (Options.SkipTreasureLoot || treasureAmount <= 0)
                {
                    return true;
                }

                var containers = new List<StorageContainer>();

                if (!SetupLootContainers(containers))
                {
                    return false;
                }

                SetTreasureLootLimit(containers);
                TakeLootFromBaseLoot();
                TakeLootFromDifficultyLoot();
                TakeLootFromDefaultLoot();
                PopulateLoot(true);
                TryAddDuplicates();
                PopulateLoot(false);

                if (Loot.Count == 0)
                {
                    Puts(mx("NoConfiguredLoot"));
                    return true;
                }

                TryRemoveDuplicates();
                VerifyLootAmount();
                SpawnLoot(containers);
                SetupSellOrders();
                return true;
            }

            private void SetupContainers()
            {
                foreach (var container in _containers)
                {
                    container.inventory.onItemAddedRemoved += new Action<Item, bool>(OnItemAddedRemoved);
                    if (container.ShortPrefabName == "box.wooden.large") container.SendNetworkUpdate();
                }
            }

            public void SetupEntity(BaseEntity e, bool skipCheck = true)
            {
                if (skipCheck)
                {
                    AddEntity(e);
                }
                else if (!MyInstance.temporaryData.NID.Contains(e.net.ID.Value))
                {
                    MyInstance.temporaryData.NID.Add(e.net.ID.Value);
                }
                MyInstance.RaidEntities[e.net.ID] = new RaidEntity(this, e);
            }

            private void SetupPickup(BaseCombatEntity e)
            {
                e.pickup.enabled = false;
            }

            private void AddContainer(StorageContainer container)
            {
                if (IsBox(container, true) || container is BuildingPrivlidge)
                {
                    _containers.Add(container);
                }

                _allcontainers.Add(container);

                AddEntity(container);
            }

            public void TryEmptyContainer(StorageContainer container)
            {
                if (Options.EmptyAll && !Options.EmptyExemptions.Exists(container.ShortPrefabName.Contains))
                {
                    ClearInventory(container.inventory);
                    ItemManager.DoRemoves();
                }
                container.dropsLoot = false;
                container.dropFloats = false;
            }

            private void SetupContainer(StorageContainer container)
            {
                AddContainer(container);

                if (container.inventory == null)
                {
                    container.inventory = new ItemContainer();
                    container.inventory.ServerInitialize(null, 48);
                    container.inventory.GiveUID();
                    container.inventory.entityOwner = container;
                }
                else TryEmptyContainer(container);
                
                if (Options.LockBoxes && IsBox(container, false) || Options.LockLockers && container is Locker)
                {
                    CreateLock(container);
                }

                SetupBoxSkin(container);

                container.dropsLoot = false;
                container.dropFloats = false;

                if (container is BuildingPrivlidge)
                {
                    container.dropsLoot = config.Settings.Management.AllowCupboardLoot;
                }
                else if (!IsProtectedWeapon(container) && !(container is VendingMachine))
                {
                    container.dropsLoot = true;
                }
                //else container.isLootable = false;

                if (IsBox(container, false) || container is BuildingPrivlidge)
                {
                    container.inventory.SetFlag(ItemContainer.Flag.NoItemInput, Options.NoItemInput);
                }
            }

            private void SetupIO(ContainerIOEntity io)
            {
                io.dropFloats = false;
                io.dropsLoot = !IsProtectedWeapon(io);
                io.inventory.SetFlag(ItemContainer.Flag.NoItemInput, true);
            }

            private void SetupIO(IOEntity io)
            {
                io.SetFlag(BaseEntity.Flags.Reserved8, true, false, true);
            }

            private void SetupLock(BaseEntity e, bool justCreated = false)
            {
                AddEntity(e);
                locks.Add(e);

                if (e.IsValid())
                {
                    MyInstance.RaidEntities[e.net.ID] = new RaidEntity(this, e);
                }

                if (e is CodeLock)
                {
                    var codeLock = e as CodeLock;

                    if (config.Settings.Management.RandomCodes || justCreated)
                    {
                        codeLock.code = UnityEngine.Random.Range(1000, 9999).ToString();
                        codeLock.hasCode = true;
                    }

                    codeLock.OwnerID = 0;
                    codeLock.guestCode = string.Empty;
                    codeLock.hasGuestCode = false;
                    codeLock.guestPlayers.Clear();
                    codeLock.whitelistPlayers.Clear();
                    codeLock.SetFlag(BaseEntity.Flags.Locked, true);
                }
                else if (e is KeyLock)
                {
                    var keyLock = e as KeyLock;

                    if (config.Settings.Management.RandomCodes)
                    {
                        keyLock.keyCode = UnityEngine.Random.Range(1, 100000);
                    }

                    keyLock.OwnerID = 0;
                    keyLock.firstKeyCreated = true;
                    keyLock.SetFlag(BaseEntity.Flags.Locked, true);
                }
            }

            private void SetupVendingMachine(VendingMachine vm)
            {
                vms.Add(vm);

                vm.SetFlag(BaseEntity.Flags.Reserved4, config.Settings.Management.AllowBroadcasting, false, true);
                vm.FullUpdate();
            }

            private void SetupLight(IOEntity light)
            {
                if (light == null || !config.Settings.Management.Lights && !config.Settings.Management.AlwaysLights)
                {
                    return;
                }

                lights.Add(light);
            }

            private void SetupHBHFSensor(HBHFSensor sensor)
            {
                triggers[sensor.myTrigger] = sensor;
                SetupIO(sensor);
                sensor.SetFlag(HBHFSensor.Flag_IncludeAuthed, true, false, true);
                sensor.SetFlag(HBHFSensor.Flag_IncludeOthers, true, false, true);
            }

            private void SetupBattery(ElectricBattery eb)
            {
                eb.rustWattSeconds = eb.maxCapactiySeconds - 1f;
            }

            private void SetupGenerator(ElectricGenerator generator)
            {
                generator.electricAmount = config.Weapons.TestGeneratorPower;
            }

            private void SetupButton(PressButton button)
            {
                button._maxHealth = Options.Elevators.ButtonHealth;
                button.InitializeHealth(Options.Elevators.ButtonHealth, Options.Elevators.ButtonHealth);
            }

            private void SetupBuildingBlock(BuildingBlock block)
            {
                if (block.IsKilled())
                {
                    return;
                }

                if (Options.Blocks.Any())
                {
                    ChangeTier(block);
                }

                block.StopBeingDemolishable();
                block.StopBeingRotatable();
            }

            private void ChangeTier(BuildingBlock block)
            {
                if (Options.Blocks.HQM && block.grade != BuildingGrade.Enum.TopTier)
                {
                    SetGrade(block, BuildingGrade.Enum.TopTier);
                }
                else if (Options.Blocks.Metal && block.grade != BuildingGrade.Enum.Metal)
                {
                    SetGrade(block, BuildingGrade.Enum.Metal);
                }
                else if (Options.Blocks.Stone && block.grade != BuildingGrade.Enum.Stone)
                {
                    SetGrade(block, BuildingGrade.Enum.Stone);
                }
                else if (Options.Blocks.Wooden && block.grade != BuildingGrade.Enum.Wood)
                {
                    SetGrade(block, BuildingGrade.Enum.Wood);
                }
            }

            private void SetGrade(BuildingBlock block, BuildingGrade.Enum grade)
            {
                block.SetGrade(grade);
                block.SetHealthToMax();
                block.SendNetworkUpdate();
                block.UpdateSkin();
            }

            private void SetupTeslaCoil(TeslaCoil tc)
            {
                if (!config.Weapons.TeslaCoil.RequiresPower)
                {
                    tc.UpdateFromInput(25, 0);
                    tc.SetFlag(IOEntity.Flag_HasPower, true, false, true);
                }

                tc.InitializeHealth(config.Weapons.TeslaCoil.Health, config.Weapons.TeslaCoil.Health);
                tc.maxDischargeSelfDamageSeconds = Mathf.Clamp(config.Weapons.TeslaCoil.MaxDischargeSelfDamageSeconds, 0f, 9999f);
                tc.maxDamageOutput = Mathf.Clamp(config.Weapons.TeslaCoil.MaxDamageOutput, 0f, 9999f);
            }

            private void SetupIgniter(Igniter igniter)
            {
                igniter.SelfDamagePerIgnite = 0f;
            }

            private void SetupTurret(AutoTurret turret)
            {
                if (IsUnloading || turret.IsKilled())
                {
                    return;
                }

                if (config.Settings.Management.ClippedTurrets && turret.RCEyes != null)
                {
                    var position = turret.RCEyes.position;

                    if (TestClippedInside(position, 0.5f, Layers.Mask.Terrain) || IsRockFaceUpwardsSecondary(position))
                    {
                        Entities.Remove(turret);
                        turret.dropsLoot = false;
                        Interface.Oxide.NextTick(turret.SafelyKill);
                        return;
                    }
                }

                if (turret is NPCAutoTurret)
                {
                    BMGELEVATOR.RemoveImmortality(turret.baseProtection, 0.0f, 0.9f, 0.0f, 1.0f, 0.5f, 0.9f, 1.0f, 1.0f, 1.0f, 0.0f, 1.0f, 1.0f, 0.0f, 1.0f, 0.0f, 1.0f, 0.8f, 1.0f, 1.0f, 1.0f, 1.0f, 0.5f, 0.5f, 1.0f, 1.0f);
                }

                SetupIO(turret as IOEntity);

                Options.AutoTurret.Shortnames.Remove("fun.trumpet");
                turrets.Add(turret);

                turret.authorizedPlayers.Clear();
                turret.InitializeHealth(Options.AutoTurret.Health, Options.AutoTurret.Health);
                turret.sightRange = Options.AutoTurret.SightRange;
                turret.aimCone = Options.AutoTurret.AimCone;

                if (Options.AutoTurret.RemoveWeapon)
                {
                    turret.AttachedWeapon = null;
                    Item slot = turret.inventory.GetSlot(0);

                    if (slot != null && (slot.info.category == ItemCategory.Weapon || slot.info.category == ItemCategory.Fun))
                    {
                        slot.RemoveFromContainer();
                        slot.Remove();
                    }
                }

                if (Options.AutoTurret.Hostile)
                {
                    turret.SetPeacekeepermode(false);
                }

                if (config.Weapons.InfiniteAmmo.AutoTurret)
                {
                    turret.inventory.onPreItemRemove += new Action<Item>(OnWeaponItemPreRemove);
                }
            }

            private void SetupTurrets()
            {
                turretsCoroutine = ServerMgr.Instance.StartCoroutine(SetupTurretsHelper());
            }

            private IEnumerator SetupTurretsHelper()
            {
                if (Options.AutoTurret.InitiateOnSpawn)
                {
                    while (IsLoading)
                    {
                        yield return CoroutineEx.waitForSeconds(0.1f);
                    }
                }

                foreach (var turret in turrets)
                {
                    yield return TurretCommand(turret, () => EquipTurretWeapon(turret));

                    yield return TurretCommand(turret, () => turret.UpdateAttachedWeapon());

                    yield return TurretCommand(turret, () => FillAmmoTurret(turret));

                    if (!Options.AutoTurret.RequiresPower)
                    {
                        yield return TurretCommand(turret, () => turret.InitiateStartup());
                    }
                }

                turretsCoroutine = null;
            }

            private IEnumerator TurretCommand(AutoTurret turret, Action action)
            {
                yield return CoroutineEx.waitForSeconds(0.025f);
                if (!turret.IsKilled()) action();
            }

            private bool CanBypassAuthorized(ulong userid) => userid.BelongsToGroup("admin") || userid.HasPermission("raidablebases.canbypass");

            private void EquipTurretWeapon(AutoTurret turret)
            {
                if (Options.AutoTurret.Shortnames.Count > 0 && turret.AttachedWeapon.IsNull())
                {
                    var shortname = Options.AutoTurret.Shortnames.GetRandom();
                    var itemToCreate = ItemManager.FindItemDefinition(shortname);

                    if (itemToCreate != null)
                    {
                        Item item = ItemManager.Create(itemToCreate, 1, (ulong)itemToCreate.skins.GetRandom().id);

                        if (!item.MoveToContainer(turret.inventory, 0, false))
                        {
                            item.Remove();
                        }
                        else
                        {
                            item.SwitchOnOff(true);
                        }
                    }
                }
            }

            private void SetupGunTrap(GunTrap gt)
            {
                if (config.Weapons.Ammo.GunTrap > 0)
                {
                    FillAmmoGunTrap(gt);
                }

                if (config.Weapons.InfiniteAmmo.GunTrap)
                {
                    gt.inventory.onPreItemRemove += new Action<Item>(OnWeaponItemPreRemove);
                }

                triggers[gt.trigger] = gt;
            }

            private void SetupFogMachine(FogMachine fm)
            {
                if (config.Weapons.Ammo.FogMachine > 0)
                {
                    FillAmmoFogMachine(fm);
                }

                if (config.Weapons.InfiniteAmmo.FogMachine)
                {
                    fm.fuelPerSec = 0f;
                }

                if (config.Weapons.FogMotion)
                {
                    fm.SetFlag(BaseEntity.Flags.Reserved9, true, false, true);
                }

                if (!config.Weapons.FogRequiresPower)
                {
                    fm.CancelInvoke(fm.CheckTrigger);
                    fm.SetFlag(BaseEntity.Flags.Reserved5, b: true);
                    fm.SetFlag(BaseEntity.Flags.Reserved6, b: true);
                    fm.SetFlag(BaseEntity.Flags.Reserved10, b: true);
                    fm.SetFlag(BaseEntity.Flags.On, true, false, true);
                }
            }

            private void SetupFlameTurret(FlameTurret ft)
            {
                triggers[ft.trigger] = ft;
                ft.InitializeHealth(Options.FlameTurretHealth, Options.FlameTurretHealth);

                if (config.Weapons.Ammo.FlameTurret > 0)
                {
                    FillAmmoFlameTurret(ft);
                }

                if (config.Weapons.InfiniteAmmo.FlameTurret)
                {
                    ft.fuelPerSec = 0f;
                }
            }

            private void SetupSamSite(SamSite ss)
            {
                samsites.Add(ss);

                ss.vehicleScanRadius = ss.missileScanRadius = config.Weapons.SamSiteRange;

                if (config.Weapons.SamSiteRepair > 0f)
                {
                    ss.staticRespawn = true;
                    ss.InvokeRepeating(ss.SelfHeal, config.Weapons.SamSiteRepair * 60f, config.Weapons.SamSiteRepair * 60f);
                }
                else ss.staticRespawn = false;

                if (!config.Weapons.SamSiteRequiresPower)
                {
                    SetupIO(ss as IOEntity);
                }

                if (config.Weapons.Ammo.SamSite > 0)
                {
                    FillAmmoSamSite(ss);
                }

                if (config.Weapons.InfiniteAmmo.SamSite)
                {
                    ss.inventory.onPreItemRemove += new Action<Item>(OnWeaponItemPreRemove);
                }
            }

            private bool ChangeTier(Door door)
            {
                uint prefabID = 0u;

                switch (door.ShortPrefabName)
                {
                    case "door.hinged.toptier":
                        if (Options.Doors.Metal) prefabID = 202293038;
                        else if (Options.Doors.Wooden) prefabID = 1343928398;
                        break;
                    case "door.hinged.metal":
                    case "door.hinged.industrial.a":
                    case "door.hinged.industrial.d":
                        if (Options.Doors.HQM) prefabID = 170207918;
                        else if (Options.Doors.Wooden) prefabID = 1343928398;
                        break;
                    case "door.hinged.wood":
                        if (Options.Doors.HQM) prefabID = 170207918;
                        else if (Options.Doors.Metal) prefabID = 202293038;
                        break;
                    case "door.double.hinged.toptier":
                        if (Options.Doors.Metal) prefabID = 1418678061;
                        else if (Options.Doors.Wooden) prefabID = 43442943;
                        break;
                    case "wall.frame.garagedoor":
                        if (!Options.Doors.GarageDoor) return false;
                        if (Options.Doors.HQM) prefabID = 201071098;
                        else if (Options.Doors.Wooden) prefabID = 43442943;
                        break;
                    case "door.double.hinged.metal":
                        if (Options.Doors.HQM) prefabID = 201071098;
                        else if (Options.Doors.Wooden) prefabID = 43442943;
                        break;
                    case "door.double.hinged.wood":
                        if (Options.Doors.HQM) prefabID = 201071098;
                        else if (Options.Doors.Metal) prefabID = 1418678061;
                        break;
                }

                return prefabID != 0u && SetDoorType(door, prefabID);
            }

            private bool SetDoorType(Door door, uint prefabID)
            {
                var door2 = GameManager.server.CreateEntity(StringPool.Get(prefabID), door.transform.position, door.transform.rotation) as Door;

                door.SafelyKill();
                door2.Spawn();

                if (CanSetupEntity(door2))
                {
                    SetupEntity(door2);
                    SetupDoor(door2, true);
                }

                return true;
            }

            private void SetupDoor(Door door, bool changed = false)
            {
                if (Options.DoorLock || Options.KeyLock)
                {
                    CreateLock(door);
                }

                if (!changed && Options.Doors.Any() && ChangeTier(door))
                {
                    return;
                }

                SetupSkin(door);

                if (Options.CloseOpenDoors)
                {
                    door.SetOpen(false, true);
                }
            }

            private void SetupDoors()
            {
                doors.RemoveAll(x => x.IsKilled());

                foreach (var door in doors)
                {
                    SetupDoor(door);
                }
            }

            private void SetupDoorControllers()
            {
                doorControllers.RemoveAll(x => x.IsKilled());

                foreach (var cdm in doorControllers)
                {
                    SetupIO(cdm);

                    if (cdm.IsPaired())
                    {
                        doors.Remove(cdm.targetDoor);
                        continue;
                    }

                    var door = cdm.FindDoor(true);

                    if (door.IsReallyValid())
                    {
                        cdm.SetTargetDoor(door);
                        doors.Remove(door);

                        if (door.isSecurityDoor || !door.canTakeLock)
                        {
                            continue;
                        }

                        if (Options.DoorLock || Options.KeyLock)
                        {
                            CreateLock(door);
                        }
                    }
                }

                doorControllers.Clear();
            }

            private void CreateLock(BaseEntity entity)
            {
                if (entity.IsKilled())
                {
                    return;
                }

                var slot = entity.GetSlot(BaseEntity.Slot.Lock);

                if (slot.IsNull())
                {
                    CreateCodeLock(entity);
                    return;
                }

                if (Options.KeyLock)
                {
                    CodeLock codeLock;
                    if (slot.TryGetComponent(out codeLock))
                    {
                        codeLock.SetParent(null);
                        codeLock.SafelyKill();
                    }

                    KeyLock keyLock;
                    if (!slot.TryGetComponent(out keyLock))
                    {
                        CreateKeyLock(entity);
                    }
                    else SetupLock(keyLock);
                }
                else if (Options.DoorLock)
                {
                    KeyLock keyLock;
                    if (slot.TryGetComponent(out keyLock))
                    {
                        keyLock.SetParent(null);
                        keyLock.SafelyKill();
                    }

                    CodeLock codeLock;
                    if (!slot.TryGetComponent(out codeLock))
                    {
                        CreateCodeLock(entity);
                    }
                    else SetupLock(codeLock, true);
                }
            }

            private void CreateKeyLock(BaseEntity entity)
            {
                var keyLock = GameManager.server.CreateEntity(StringPool.Get(2106860026)) as KeyLock;

                keyLock.gameObject.Identity();
                keyLock.SetParent(entity, entity.GetSlotAnchorName(BaseEntity.Slot.Lock));
                keyLock.Spawn();
                entity.SetSlot(BaseEntity.Slot.Lock, keyLock);

                SetupLock(keyLock, true);
            }

            private void CreateCodeLock(BaseEntity entity)
            {
                var codeLock = GameManager.server.CreateEntity(StringPool.Get(3518824735)) as CodeLock;

                codeLock.gameObject.Identity();
                codeLock.SetParent(entity, entity.GetSlotAnchorName(BaseEntity.Slot.Lock));
                codeLock.Spawn();
                entity.SetSlot(BaseEntity.Slot.Lock, codeLock);

                SetupLock(codeLock, true);
            }

            private void SetupBuildingPriviledge(BuildingPrivlidge priv)
            {
                priv.authorizedPlayers.Clear();
                priv.SendNetworkUpdate(BasePlayer.NetworkQueue.Update);

                if (Options.LockPrivilege)
                {
                    CreateLock(priv);
                }

                if (this.priv.IsKilled())
                {
                    this.priv = priv;
                }
                else if (priv.Distance(Location) < this.priv.Distance(Location))
                {
                    this.priv = priv;
                }

                privSpawned = true;
            }

            private void SetupLocker(Locker locker)
            {
                if (config.Settings.Management.Lockers)
                {
                    lockers.Add(locker);
                }
            }

            private void SetupSleepingBag(SleepingBag bag)
            {
                bag.deployerUserID = 0uL;
            }

            private void SetupMountable(BaseMountable mountable)
            {
                if (mountable.IsValid())
                {
                    Instance.MountEntities[mountable.net.ID] = new MountInfo
                    {
                        position = Location,
                        radius = ProtectionRadius,
                        mountable = mountable
                    };
                }
            }

            private void SetupCollectible(CollectibleEntity ce)
            {
                if (IsBlacklisted(ce.ShortPrefabName))
                {
                    ce.itemList = null;
                }
            }

            private void SetupSpookySpeaker(SpookySpeaker ss)
            {
                if (!config.Weapons.SpookySpeakersRequiresPower)
                {
                    ss.SetFlag(BaseEntity.Flags.On, b: true);
                    ss.InvokeRandomized(ss.SendPlaySound, ss.soundSpacing, ss.soundSpacing, ss.soundSpacingRand);
                }
            }

            private void SetupDecayEntity(DecayEntity e)
            {
                e.decay = null;
                e.upkeepTimer = float.MinValue;

                if (e is BaseTrap && !NearFoundation(e.transform.position, 1.75f))
                {
                    e.transform.position = e.transform.position.WithY(SpawnsController.GetSpawnHeight(e.transform.position, false) + 0.02f);
                }

                if (e is Barricade && !Physics.Raycast(e.transform.position + new Vector3(0f, 0.15f, 0f), Vector3.down, 50f, Layers.Mask.Construction))
                {
                    e.transform.position = e.transform.position.WithY(SpawnsController.GetSpawnHeight(e.transform.position, false));
                }
            }

            private void SetupBoxSkin(StorageContainer container)
            {
                if (!IsBox(container, false))
                {
                    return;
                }

                ItemDefinition def;
                if (!Definitions.TryGetValue(container.gameObject.name, out def))
                {
                    return;
                }

                var si = GetItemSkins(def);

                if (si.allSkins.Count == 0)
                {
                    return;
                }

                if (!skinIds.ContainsKey(container.prefabID))
                {
                    if (config.Skins.Boxes.PresetSkin == 0uL)
                    {
                        var random = new List<ulong>();

                        if (config.Skins.Boxes.RandomWorkshopSkins)
                        {
                            random.Add(si.workshopSkins.GetRandom());
                        }

                        if (config.Skins.Boxes.RandomSkins)
                        {
                            random.Add(si.skins.GetRandom());
                        }

                        if (random.Count == 0)
                        {
                            skinIds[container.prefabID] = container.skinID;
                        }
                        else skinIds[container.prefabID] = random.GetRandom();
                    }
                    else skinIds[container.prefabID] = config.Skins.Boxes.PresetSkin;
                }

                if (config.Skins.Boxes.PresetSkin != 0uL || Options.SetSkins)
                {
                    container.skinID = skinIds[container.prefabID];
                }
                else if (config.Skins.Boxes.RandomWorkshopSkins)
                {
                    container.skinID = si.workshopSkins.GetRandom();
                }
                else if (config.Skins.Boxes.RandomSkins)
                {
                    container.skinID = si.skins.GetRandom();
                }
            }

            private bool CanAcceptSkin(BaseEntity entity, ulong skin)
            {
                ItemDefinition def;
                if (!Definitions.TryGetValue(entity.gameObject.name, out def))
                {
                    return false;
                }

                return GetItemSkins(def).allSkins.Contains(skin);
            }

            private void SetupSkin(BaseEntity entity)
            {
                if (config.Skins.Deployables.Doors.Count > 0 && entity is Door)
                {
                    ulong skin = config.Skins.Deployables.Doors.GetRandom();

                    if (CanAcceptSkin(entity, skin))
                    {
                        entity.skinID = skin;
                        entity.SendNetworkUpdate();
                        return;
                    }
                }

                if (IsBox(entity, false) || config.Skins.IgnoreSkinned && entity.skinID != 0uL)
                {
                    return;
                }

                if (!config.Skins.Deployables.Everything && !config.Skins.Deployables.Names.Exists(entity.ObjectName().Contains))
                {
                    return;
                }

                ItemDefinition def;
                if (!Definitions.TryGetValue(entity.gameObject.name, out def))
                {
                    return;
                }

                var si = GetItemSkins(def);
                var random = new List<ulong>();

                if (config.Skins.Deployables.RandomWorkshopSkins && si.workshopSkins.Count > 0)
                {
                    random.Add(si.workshopSkins.GetRandom());
                }

                if (config.Skins.Loot.Imported && si.importedSkins.Count > 0)
                {
                    random.Add(si.importedSkins.GetRandom());
                }

                if (config.Skins.Deployables.RandomSkins && si.skins.Count > 0)
                {
                    random.Add(si.skins.GetRandom());
                }

                if (random.Count > 0)
                {
                    entity.skinID = random.GetRandom();
                    entity.SendNetworkUpdate();
                }
            }

            private void Subscribe()
            {
                if (IsUnloading)
                {
                    return;
                }

                if (Instance.BaseRepair.CanCall())
                {
                    Subscribe(nameof(OnBaseRepair));
                }

                if (Options.EnforceDurability)
                {
                    Subscribe(nameof(OnLoseCondition));
                    Subscribe(nameof(OnNeverWear));
                }

                if (config.Settings.Management.NoLifeSupport)
                {
                    Subscribe(nameof(OnLifeSupportSavingLife));
                }

                if (config.Settings.Management.NoDoubleJump)
                {
                    Subscribe(nameof(CanDoubleJump));
                }

                if ((Options.NPC.SpawnAmountMurderers > 0 || Options.NPC.SpawnAmountScientists > 0) && Options.NPC.Enabled)
                {
                    Options.NPC.ScientistHealth = Mathf.Clamp(Options.NPC.ScientistHealth, 1, 5000);
                    Options.NPC.MurdererHealth = Mathf.Clamp(Options.NPC.MurdererHealth, 1, 5000);
                    npcMaxAmountMurderers = Options.NPC.SpawnRandomAmountMurderers && Options.NPC.SpawnAmountMurderers > 1 ? UnityEngine.Random.Range(Options.NPC.SpawnMinAmountMurderers, Options.NPC.SpawnAmountMurderers + 1) : Options.NPC.SpawnAmountMurderers;
                    npcMaxAmountScientists = Options.NPC.SpawnRandomAmountScientists && Options.NPC.SpawnAmountScientists > 1 ? UnityEngine.Random.Range(Options.NPC.SpawnMinAmountScientists, Options.NPC.SpawnAmountScientists + 1) : Options.NPC.SpawnAmountScientists;

                    if (npcMaxAmountMurderers > 0 || npcMaxAmountScientists > 0)
                    {
                        if (config.Settings.Management.BlockNpcKits)
                        {
                            Subscribe(nameof(OnNpcKits));
                        }

                        Subscribe(nameof(OnNpcDuck));
                        Subscribe(nameof(OnNpcDestinationSet));
                        SetupNpcKits();
                        Invoke(SpawnNpcs, 1f);
                    }
                }

                if (config.Settings.Management.PreventFallDamage)
                {
                    Subscribe(nameof(OnPlayerLand));
                }

                if (!config.Settings.Management.AllowTeleport)
                {
                    Subscribe(nameof(CanTeleport));
                    Subscribe(nameof(canTeleport));
                }

                if (config.Settings.Management.BlockRestorePVP && AllowPVP || config.Settings.Management.BlockRestorePVE && !AllowPVP)
                {
                    Subscribe(nameof(OnRestoreUponDeath));
                }

                if (Options.DropTimeAfterLooting > 0 || config.UI.Containers)
                {
                    Subscribe(nameof(OnLootEntityEnd));
                }

                if (!config.Settings.Management.BackpacksOpenPVP || !config.Settings.Management.BackpacksOpenPVE)
                {
                    Subscribe(nameof(CanOpenBackpack));
                }

                if (config.Settings.Management.PreventFireFromSpreading)
                {
                    Subscribe(nameof(OnFireBallSpread));
                }

                if (Instance.IsPVE())
                {
                    Subscribe(nameof(CanEntityBeTargeted));
                    Subscribe(nameof(CanEntityTrapTrigger));
                }
                else
                {
                    Subscribe(nameof(OnTrapTrigger));
                }

                if (privSpawned)
                {
                    Subscribe(nameof(OnCupboardProtectionCalculated));
                }

                if (Options.BuildingRestrictions.Any() || !config.Settings.Management.AllowUpgrade)
                {
                    Subscribe(nameof(OnStructureUpgrade));
                }

                if (config.Settings.BlacklistedCommands.Exists(x => x.Equals("remove", StringComparison.OrdinalIgnoreCase)))
                {
                    Subscribe(nameof(canRemove));
                }

                if (Options.Invulnerable || Options.InvulnerableUntilCupboardIsDestroyed)
                {
                    Subscribe(nameof(OnEntityGroundMissing));
                }

                Subscribe(nameof(OnFireBallDamage));
                Subscribe(nameof(CanPickupEntity));
                Subscribe(nameof(OnPlayerDropActiveItem));
                Subscribe(nameof(OnPlayerDeath));
                Subscribe(nameof(OnEntityDeath));
                Subscribe(nameof(OnEntityKill));
                Subscribe(nameof(CanBGrade));
                Subscribe(nameof(CanBePenalized));
                Subscribe(nameof(CanLootEntity));
                Subscribe(nameof(OnEntityBuilt));
                Subscribe(nameof(OnCupboardAuthorize));
                Subscribe(nameof(STCanGainXP));
            }

            private void Subscribe(string hook) => Instance.Subscribe(hook);

            private void MakeAnnouncements()
            {
                var posStr = FormatGridReference(Location);

                Puts("{0} @ {1} : {2} items", BaseName, posStr, itemAmountSpawned);

                if (Options.Silent)
                {
                    return;
                }

                BaseGameMode gameMode = BaseGameMode.GetActiveGameMode(false);
                bool ingameMap = !(bool)gameMode || gameMode.ingameMap;

                foreach (var target in BasePlayer.activePlayerList)
                {
                    float distance = Mathf.Floor(target.transform.position.Distance(Location));
                    string difficultyMode = mx("Normal", target.UserIDString);
                    string flag = mx(AllowPVP ? "PVPFlag" : "PVEFlag", target.UserIDString).Replace("[", string.Empty).Replace("] ", string.Empty);
                    string api = ingameMap ? mx("RaidOpenMessage", target.UserIDString, difficultyMode, posStr, distance, flag) : mx("RaidOpenNoMapMessage", target.UserIDString, difficultyMode, distance, flag);
                    string api2 = mx("Owner", target.UserIDString);
                    string message = ownerId.IsSteamId() ? string.Format("{0}[{1} {2}]", api, api2, ownerName) : api;

                    if (config.EventMessages.OpenedPVE && !AllowPVP || config.EventMessages.OpenedPVP && AllowPVP)
                    {
                        QueueNotification(target, message);
                    }
                    else if (distance <= config.GUIAnnouncement.Distance && (config.EventMessages.OpenedPVE && !AllowPVP || config.EventMessages.OpenedPVP && AllowPVP))
                    {
                        QueueNotification(target, message);
                    }
                }
            }

            public void ResetOwner()
            {
                if (!IsOpened || !ownerId.IsSteamId() || IsPlayerActive(ownerId))
                {
                    Invoke(ResetOwner, config.Settings.Management.LockTime * 60f);
                    return;
                }

                ResetOwnerForced();
            }

            public void ResetOwnerForced()
            {
                CheckBackpacks(true);
                IsEngaged = true;
                riOwner = null;
                ownerId = 0;
                ownerName = string.Empty;
                UpdateMarker();
            }

            private void ClearLoot()
            {
                BaseLoot.Clear();
                BaseLootPermanent.Clear();
                DifficultyLoot.Clear();
                DefaultLoot.Clear();
                Collective.Clear();
                Loot.Clear();
                LootNames.Clear();
            }

            private void SpawnLoot(List<StorageContainer> containers)
            {
                if (Options.DivideLoot)
                {
                    DivideLoot(containers);
                }
                else SpawnLoot(containers, treasureAmount);

                if (itemAmountSpawned == 0)
                {
                    Puts(mx("NoLootSpawned"));
                }

                Interface.Oxide.NextTick(ClearLoot);
            }

            private void SpawnLoot(List<StorageContainer> containers, int amount)
            {
                StorageContainer container = containers.FirstOrDefault(x => x.inventory.itemList.Count + amount <= x.inventory.capacity);

                if (container == null)
                {
                    container = containers.GetRandom();
                    ClearInventory(container.inventory);
                    ItemManager.DoRemoves();
                }

                SpawnLoot(container, amount);
            }

            private void SpawnLoot(StorageContainer container, int amount)
            {
                if (amount > container.inventory.capacity)
                {
                    amount = container.inventory.capacity;
                }

                for (int j = 0; j < amount; j++)
                {
                    if (Loot.Count == 0)
                    {
                        break;
                    }

                    var lootItem = GetRandomLootItem();

                    Loot.Remove(lootItem);

                    SpawnItem(lootItem, new List<StorageContainer> { container });
                }
            }

            private LootItem GetRandomLootItem()
            {
                for (int i = 0; i < Loot.Count; i++)
                {
                    if (IsPriority(Loot[i]) || Loot[i].isModified)
                    {
                        return Loot[i];
                    }
                }

                return Loot.GetRandom();
            }

            private void DivideLoot(List<StorageContainer> containers)
            {
                while (Loot.Count > 0 && containers.Count > 0 && itemAmountSpawned < treasureAmount)
                {
                    var lootItem = GetRandomLootItem();

                    if (containers.Count > 1)
                    {
                        var lastContainer = containers[0];

                        containers.Remove(lastContainer);

                        SpawnItem(lootItem, containers);

                        containers.Insert(containers.Count, lastContainer);
                    }
                    else SpawnItem(lootItem, containers);

                    Loot.Remove(lootItem);

                    containers.RemoveAll(container => container.inventory.IsFull());
                }
            }

            private void AddToLoot(List<LootItem> source)
            {
                foreach (var ti in source)
                {
                    AddToLoot(ti);
                }

                source.Clear();
            }

            private bool AddToLoot(LootItem lootItem)
            {
                LootItem ti = lootItem.Clone();
                bool isBlueprint = ti.shortname.EndsWith(".bp");
                string shortname = isBlueprint ? ti.shortname.Replace(".bp", string.Empty) : ti.shortname;
                bool isModified = false;

                if (shortname.Contains("_") && ItemManager.FindItemDefinition(shortname) == null)
                {
                    isModified = true;
                    shortname = shortname.Substring(shortname.IndexOf("_") + 1);
                }

                if (ti.definition == null)
                {
                    Puts("Invalid shortname in config: {0} -> {1}", ti.shortname, shortname);
                    return false;
                }

                ti.isBlueprint = isBlueprint;

                int amount = ti.amount;

                if (ti.amountMin < ti.amount)
                {
                    amount = Core.Random.Range(ti.amountMin, ti.amount + 1);
                }

                if (amount <= 0)
                {
                    Loot.RemoveAll(x => lootItem.Equals(x));
                    Collective.RemoveAll(x => lootItem.Equals(x));
                    return false;
                }

                if (config.Treasure.UseStackSizeLimit || ti.stacksize != -1)
                {
                    int stackable = ti.stacksize <= 0 ? ti.definition.stackable : ti.stacksize;

                    if (!isModified) isModified = amount > stackable;

                    foreach (int stack in GetStacks(amount, stackable))
                    {
                        Loot.Add(new LootItem(shortname, stack, stack, ti.skin, isBlueprint, ti.probability, ti.stacksize, ti.name, isModified));
                    }
                }
                else Loot.Add(new LootItem(shortname, amount, amount, ti.skin, isBlueprint, ti.probability, ti.stacksize, ti.name, isModified));
                return true;
            }

            private List<int> GetStacks(int amount, int maxStack)
            {
                var stacks = new List<int>();

                while (amount > maxStack && stacks.Count < 100)
                {
                    amount -= maxStack;
                    stacks.Add(maxStack);
                }

                if (amount > 0)
                {
                    stacks.Add(amount);
                }

                return stacks;
            }

            private void TakeLootFrom(List<LootItem> source, List<LootItem> to, bool isUnique)
            {
                if (source.Count == 0)
                {
                    return;
                }

                var from = new List<LootItem>();

                foreach (var ti in source)
                {
                    if (ti == null || ti.amount <= 0 || ti.probability <= 0f)
                    {
                        continue;
                    }

                    Collective.Add(ti.Clone());
                    from.Add(ti.Clone());
                }

                if (from.Count == 0)
                {
                    return;
                }

                Shuffle(from);

                foreach (var ti in from)
                {
                    if (ti.probability == 1f || UnityEngine.Random.value <= ti.probability)
                    {
                        to.Add(ti.Clone());
                    }
                }

                if (Options.Multiplier != 1f)
                {
                    var m = Mathf.Clamp(Options.Multiplier, 0f, 999f);

                    foreach (var ti in to)
                    {
                        if (ti.amount > 1)
                        {
                            ti.amount = Mathf.CeilToInt(ti.amount * m);
                            ti.amountMin = Mathf.CeilToInt(ti.amountMin * m);
                        }
                    }
                }
            }

            private bool SetupLootContainers(List<StorageContainer> containers)
            {
                if (_containers.Count == 0)
                {
                    Puts(mx(Entities.Exists() ? "NoContainersFound" : "NoEntitiesFound", null, BaseName, PositionToGrid(Location)));
                    return false;
                }

                CheckExpansionSettings();

                foreach (var container in _containers.ToList())
                {
                    if (!IsBox(container, true) || Options.IgnoreContainedLoot && !container.inventory.IsEmpty())
                    {
                        continue;
                    }

                    if (config.Settings.Management.ClippedBoxes && IsRockFaceUpwardsSecondary(container.transform.position + new Vector3(0f, container.bounds.extents.y, 0f)))
                    {
                        _allcontainers.Remove(container);
                        _containers.Remove(container);
                        Entities.Remove(container);
                        container.dropsLoot = false;
                        Interface.Oxide.NextTick(container.SafelyKill);
                        continue;
                    }

                    containers.Add(container);
                }

                if (Options.IgnoreContainedLoot)
                {
                    lockers.RemoveAll(x => !x.inventory.IsEmpty());
                }

                if (containers.Count == 0)
                {
                    Puts(mx("NoBoxesFound", null, BaseName, PositionToGrid(Location)));
                    return false;
                }

                return true;
            }

            private void SetTreasureLootLimit(List<StorageContainer> containers)
            {
                if (treasureAmount <= 400)
                {
                    return;
                }

                int availableSpace = privSpawned && config.Settings.Management.Cupboard ? 24 : 0;

                foreach (var container in containers)
                {
                    availableSpace += container.InventorySlots();
                }

                if (config.Settings.Management.Lockers)
                {
                    foreach (var container in lockers)
                    {
                        availableSpace += container.InventorySlots();
                    }
                }

                if (config.Settings.Management.Cook)
                {
                    foreach (var container in ovens)
                    {
                        availableSpace += container.InventorySlots();
                    }
                }

                if (config.Settings.Management.Food)
                {
                    foreach (var container in _allcontainers)
                    {
                        if (container.IsKilled() || container.ShortPrefabName != "fridge.deployed") continue;
                        availableSpace += container.InventorySlots();
                    }

                    foreach (var container in ovens)
                    {
                        if (container.IsKilled() || !container.ShortPrefabName.Contains("bbq")) continue;
                        availableSpace += container.InventorySlots();
                    }
                }

                if (treasureAmount > availableSpace)
                {
                    treasureAmount = availableSpace;
                }
            }

            private void TakeLootFromBaseLoot()
            {
                TakeLootFrom(Instance.BaseLootList.ToList(), BaseLoot, config.Treasure.UniqueBaseLoot);

                BaseLootPermanent = BaseLoot.ToList();
            }

            private void TakeLootFromDifficultyLoot()
            {
                if (BaseLoot.Count < treasureAmount && Instance.Buildings.DifficultyLootLists.ContainsKey(RaidableMode.Normal))
                {
                    TakeLootFrom(Instance.Buildings.DifficultyLootLists[RaidableMode.Normal], DifficultyLoot, config.Treasure.UniqueDifficultyLoot);
                }
            }

            private void TakeLootFromDefaultLoot()
            {
                if (BaseLoot.Count + DifficultyLoot.Count < treasureAmount)
                {
                    TakeLootFrom(TreasureLoot, DefaultLoot, config.Treasure.UniqueDefaultLoot);
                }

                if (BaseLoot.Count + DifficultyLoot.Count + DefaultLoot.Count < treasureAmount)
                {
                    TakeLootFrom(WeekdayLoot, DefaultLoot, config.Treasure.UniqueDefaultLoot);
                }
            }

            private void PopulateLoot(bool unique)
            {
                if (!unique || !config.Treasure.UniqueBaseLoot)
                {
                    AddToLoot(BaseLoot);
                }

                if (!unique || !config.Treasure.UniqueDifficultyLoot)
                {
                    AddToLoot(DifficultyLoot);
                }

                if (!unique || !config.Treasure.UniqueDefaultLoot)
                {
                    AddToLoot(DefaultLoot);
                }
            }

            private void TryAddDuplicates()
            {
                if (Options.AllowDuplicates && Loot.Count > 0 && Loot.Count < treasureAmount)
                {
                    int attempts = treasureAmount;

                    while (Loot.Count < treasureAmount && Collective.Count > 0 && --attempts > 0)
                    {
                        var ti = Collective.GetRandom();

                        if (IsUnique(ti) || !AddToLoot(ti))
                        {
                            Collective.Remove(ti);
                        }
                    }
                }
            }

            private void TryRemoveDuplicates()
            {
                if (!Options.AllowDuplicates)
                {
                    var newLoot = new List<LootItem>();

                    foreach (var ti in Loot)
                    {
                        if (ti.isModified || !LootNames.Contains(ti.shortname) || IsPriority(ti))
                        {
                            LootNames.Add(ti.shortname);
                            newLoot.Add(ti);
                        }
                    }

                    Loot = newLoot;
                }

                foreach (var ti in Loot)
                {
                    LootNames.Add(ti.shortname);
                }
            }

            private bool IsPriority(LootItem a)
            {
                return Options.AlwaysSpawn && BaseLootPermanent.Exists(b => a.shortname == b.shortname);
            }

            private bool IsUnique(LootItem ti)
            {
                if (!Options.AllowDuplicates && Loot.Exists(x => x.shortname == ti.shortname))
                {
                    return true;
                }

                if (config.Treasure.UniqueBaseLoot && BaseLootPermanent.Exists(x => x.Equals(ti)))
                {
                    return true;
                }

                if (config.Treasure.UniqueDifficultyLoot && DifficultyLoot.Exists(x => x.Equals(ti)))
                {
                    return true;
                }

                if (config.Treasure.UniqueDefaultLoot && DefaultLoot.Exists(x => x.Equals(ti)))
                {
                    return true;
                }

                return false;
            }

            private void VerifyLootAmount()
            {
                if (Loot.Count > treasureAmount)
                {
                    Shuffle(Loot);

                    int index = Loot.Count;

                    while (Loot.Count > treasureAmount && --index >= 0)
                    {
                        if (!IsPriority(Loot[index]))
                        {
                            Loot.RemoveAt(index);
                        }
                    }
                }
                else
                {
                    int retries = treasureAmount - Loot.Count;

                    while (Loot.Count < treasureAmount && Collective.Count > 0 && --retries > 0)
                    {
                        var ti = Collective.GetRandom();

                        if (IsUnique(ti))
                        {
                            Collective.Remove(ti);
                            continue;
                        }

                        LootNames.Add(ti.shortname);
                        AddToLoot(ti);
                        retries++;
                    }
                }
            }

            private void SetupSellOrders()
            {
                if (!config.Settings.Management.Inherit.Exists("vendingmachine".Contains))
                {
                    return;
                }

                vms.RemoveAll(vm => vm.IsKilled());

                foreach (var vm in vms)
                {
                    vm.InstallDefaultSellOrders();
                    vm.SetFlag(BaseEntity.Flags.Reserved4, config.Settings.Management.AllowBroadcasting, false, true);

                    foreach (Item item in vm.inventory.itemList)
                    {
                        if (vm.sellOrders.sellOrders.Count < 8)
                        {
                            ItemDefinition itemToSellDef = ItemManager.FindItemDefinition(item.info.itemid);
                            ItemDefinition currencyDef = ItemManager.FindItemDefinition(-932201673);

                            if (!(itemToSellDef == null) && !(currencyDef == null))
                            {
                                int itemToSellAmount = Mathf.Clamp(item.amount, 1, itemToSellDef.stackable);

                                vm.sellOrders.sellOrders.Add(new ProtoBuf.VendingMachine.SellOrder
                                {
                                    ShouldPool = false,
                                    itemToSellID = item.info.itemid,
                                    itemToSellAmount = itemToSellAmount,
                                    currencyID = -932201673,
                                    currencyAmountPerItem = 999999,
                                    currencyIsBP = true,
                                    itemToSellIsBP = item.IsBlueprint()
                                });

                                vm.RefreshSellOrderStockLevel(itemToSellDef);
                            }
                        }
                    }

                    vm.FullUpdate();
                }
            }

            private List<LootItem> BaseLoot { get; set; } = new List<LootItem>();
            private List<LootItem> BaseLootPermanent { get; set; } = new List<LootItem>();
            private List<LootItem> Collective { get; set; } = new List<LootItem>();
            private List<LootItem> DifficultyLoot { get; set; } = new List<LootItem>();
            private List<LootItem> DefaultLoot { get; set; } = new List<LootItem>();
            private List<LootItem> Loot { get; set; } = new List<LootItem>();
            private HashSet<string> LootNames { get; set; } = new HashSet<string>();

            private void SpawnItem(LootItem ti, ItemContainer[] containers)
            {
                if (ti.amountMin < ti.amount)
                {
                    ti.amount = Core.Random.Range(ti.amountMin, ti.amount + 1);
                }

                Item item = CreateItem(ti);

                if (item == null || item.MoveToContainer(containers[0]) || item.MoveToContainer(containers[1]) || item.MoveToContainer(containers[2]))
                {
                    return;
                }

                item.Remove();
            }

            private void SpawnItem(LootItem ti, List<StorageContainer> containers)
            {
                Item item = CreateItem(ti);

                if (item == null)
                {
                    return;
                }

                foreach (var container in containers)
                {
                    if (MoveToCupboard(item) || MoveToBBQ(item) /*|| MoveToOven(item)*/ || MoveFood(item) || MoveToLocker(item))
                    {
                        itemAmountSpawned++;
                        return;
                    }
                    else if (container is BaseOven && !IsCookable(item.info))
                    {
                        continue;
                    }
                    else if (item.MoveToContainer(container.inventory, -1, false))
                    {
                        itemAmountSpawned++;
                        return;
                    }
                }

                item.Remove();
            }

            private Item CreateItem(LootItem ti)
            {
                if (ti.amount <= 0)
                {
                    return null;
                }

                if (ti.definition == null)
                {
                    Puts("Invalid shortname in config: {0}", ti.shortname);
                    return null;
                }

                var def = ti.definition;
                ulong skin = GetItemSkin(def, ti.skin, true);

                Item item;
                if (ti.isBlueprint)
                {
                    item = ItemManager.Create(Workbench.GetBlueprintTemplate());
                    item.blueprintTarget = def.itemid;
                    item.amount = ti.amount;
                }
                else item = ItemManager.Create(def, ti.amount, skin);

                if (!string.IsNullOrEmpty(ti.name))
                {
                    item.name = ti.name;
                }

                var e = item.GetHeldEntity();

                if (e.IsReallyValid())
                {
                    e.skinID = skin;
                    e.SendNetworkUpdate();
                }

                return item;
            }

            private bool MoveFood(Item item)
            {
                if (!config.Settings.Management.Food || _allcontainers.Count == 0 || item.info.category != ItemCategory.Food)
                {
                    return false;
                }

                if (config.Settings.Management.Foods.Exists(item.info.shortname.Contains))
                {
                    return false;
                }

                if (_allcontainers.Count <= 1)
                {
                    return false;
                }

                var fridges = _allcontainers.Where(x => !x.IsKilled() && x.ShortPrefabName == "fridge.deployed");

                if (fridges.Count > 1)
                {
                    Shuffle(fridges);
                }

                foreach (var x in fridges)
                {
                    if (item.MoveToContainer(x.inventory, -1, true))
                    {
                        return true;
                    }
                }

                return false;
            }

            private bool MoveToBBQ(Item item)
            {
                if (!config.Settings.Management.Food || ovens.Count == 0 || item.info.category != ItemCategory.Food || !IsCookable(item.info))
                {
                    return false;
                }

                if (config.Settings.Management.Foods.Exists(item.info.shortname.Contains))
                {
                    return false;
                }

                if (ovens.Count > 1)
                {
                    Shuffle(ovens);
                }

                foreach (var oven in ovens)
                {
                    if (oven.IsKilled())
                    {
                        continue;
                    }

                    if (oven.ShortPrefabName.Contains("bbq") && item.MoveToContainer(oven.inventory, -1, true))
                    {
                        return true;
                    }
                }

                return false;
            }

            private bool MoveToCupboard(Item item)
            {
                if (!config.Settings.Management.Cupboard || !privSpawned || item.info.category != ItemCategory.Resources || config.Treasure.ExcludeFromCupboard.Contains(item.info.shortname))
                {
                    return false;
                }

                if (config.Settings.Management.Cook && item.info.shortname.EndsWith(".ore") && MoveToOven(item))
                {
                    return true;
                }

                return !priv.IsKilled() && item.MoveToContainer(priv.inventory, -1, true);
            }

            private bool IsCookable(ItemDefinition def)
            {
                if (def.shortname.EndsWith(".cooked") || def.shortname.EndsWith(".burned") || def.shortname.EndsWith(".spoiled") || def.shortname == "lowgradefuel")
                {
                    return false;
                }

                return def.GetComponent<ItemModCookable>() || def.shortname == "wood";
            }

            private bool MoveToOven(Item item)
            {
                if (!config.Settings.Management.Cook || ovens.Count == 0 || !IsCookable(item.info))
                {
                    return false;
                }

                if (ovens.Count > 1)
                {
                    Shuffle(ovens);
                }

                foreach (var oven in ovens)
                {
                    if (oven.IsKilled() || oven.ShortPrefabName.Contains("bbq"))
                    {
                        continue;
                    }

                    if (item.info.shortname.EndsWith(".ore") && !oven.ShortPrefabName.Contains("furnace"))
                    {
                        continue;
                    }

                    if (item.info.shortname == "lowgradefuel" && !oven.ShortPrefabName.Contains("tunalight") && !oven.ShortPrefabName.Contains("lantern"))
                    {
                        continue;
                    }

                    if (item.info.shortname == "crude.oil" && !oven.ShortPrefabName.Contains("refinery"))
                    {
                        continue;
                    }

                    if (item.MoveToContainer(oven.inventory, -1, true))
                    {
                        if (!oven.IsOn() && oven.FindBurnable() != null)
                        {
                            oven.SetFlag(BaseEntity.Flags.On, true, false, true);
                        }

                        if (oven.IsOn() && !item.HasFlag(global::Item.Flag.OnFire))
                        {
                            item.SetFlag(global::Item.Flag.OnFire, true);
                            item.MarkDirty();
                        }

                        return true;
                    }
                }

                return false;
            }

            private Dictionary<ItemDefinition, Wearable> _wearables = new Dictionary<ItemDefinition, Wearable>();

            private bool IsWearable(ItemDefinition def, Wearable.OccupationSlots occupationOver)
            {
                Wearable wearable;
                if (!_wearables.TryGetValue(def, out wearable))
                {
                    ItemModWearable itemModWearable = def.GetComponent<ItemModWearable>();
                    if (itemModWearable == null) return false;
                    wearable = itemModWearable.targetWearable;
                    if (wearable == null) return false;
                    _wearables[def] = wearable;
                }
                return (wearable.occupationOver & (occupationOver)) != 0;
            }

            private bool IsHealthy(Item item)
            {
                if (item.info.category == ItemCategory.Food || item.info.category == ItemCategory.Medical)
                {
                    if (item.info.shortname.Contains(".spoiled") || item.info.shortname.Contains(".raw") || item.info.shortname.Contains(".burned"))
                    {
                        return false;
                    }

                    return item.info.GetComponent<ItemModConsumable>() != null;
                }

                return false;
            }

            private bool IsRangedWeapon(Item item) => item.info.category == ItemCategory.Weapon && item.GetHeldEntity() is BaseProjectile;

            private bool IsHeadwear(ItemDefinition def) => IsWearable(def, Wearable.OccupationSlots.HeadTop | Wearable.OccupationSlots.Face | Wearable.OccupationSlots.HeadBack) || def.shortname == "gloweyes";

            private bool IsBoots(ItemDefinition def) => IsWearable(def, Wearable.OccupationSlots.LeftFoot | Wearable.OccupationSlots.RightFoot);

            private bool IsGloves(ItemDefinition def) => IsWearable(def, Wearable.OccupationSlots.LeftHand | Wearable.OccupationSlots.RightHand) || def.shortname.Contains("gloves");

            private bool IsTorso(ItemDefinition def) => IsWearable(def, Wearable.OccupationSlots.TorsoBack | Wearable.OccupationSlots.TorsoFront) || def.shortname.Contains("vest") || def.shortname.Contains("hoodie") || def.shortname.Contains("suit");

            private bool IsPants(ItemDefinition def) => IsWearable(def, Wearable.OccupationSlots.LeftLeg | Wearable.OccupationSlots.RightLeg) || def.shortname.Contains("pants") || def.shortname.Contains("trousers");

            private bool MoveToLocker(Item item)
            {
                if (!config.Settings.Management.Lockers || lockers.Count == 0)
                {
                    return false;
                }

                foreach (var locker in lockers)
                {
                    if (locker.IsKilled())
                    {
                        continue;
                    }

                    if (IsHeadwear(item.info) && MoveToContainer(locker.inventory, item, new int[] { 0, 13, 26 }))
                    {
                        return true;
                    }
                    else if (IsBoots(item.info) && MoveToContainer(locker.inventory, item, new int[] { 1, 14, 27 }))
                    {
                        return true;
                    }
                    else if (IsGloves(item.info) && MoveToContainer(locker.inventory, item, new int[] { 2, 15, 28 }))
                    {
                        return true;
                    }
                    else if (IsTorso(item.info) && MoveToContainer(locker.inventory, item, new int[] { 3, 16, 29 }))
                    {
                        return true;
                    }
                    else if (IsPants(item.info) && MoveToContainer(locker.inventory, item, new int[] { 4, 17, 30 }))
                    {
                        return true;
                    }
                    else if (item.info.shortname.Contains("shirt") && MoveToContainer(locker.inventory, item, new int[] { 5, 18, 31 }))
                    {
                        return true;
                    }
                    else if (item.IsBlueprint() && item.info.Blueprint.NeedsSteamDLC && MoveToContainer(locker.inventory, item, new int[] { 6, 19, 32 }))
                    {
                        return true;
                    }
                    else if (IsRangedWeapon(item) && MoveToContainer(locker.inventory, item, new int[] { 7, 8, 20, 21, 33, 34 }))
                    {
                        return true;
                    }
                    else if (item.info.category == ItemCategory.Ammunition && MoveToContainer(locker.inventory, item, new int[] { 9, 10, 22, 23, 35, 36 }))
                    {
                        return true;
                    }
                    else if (IsHealthy(item) && MoveToContainer(locker.inventory, item, new int[] { 11, 12, 24, 25, 37, 38 }))
                    {
                        return true;
                    }
                }

                return false;
            }

            private bool MoveToContainer(ItemContainer container, Item item, int[] positions)
            {
                foreach (int position in positions)
                {
                    if (item.MoveToContainer(container, position, false))
                    {
                        return true;
                    }
                }

                return false;
            }

            private void CheckExpansionSettings()
            {
                if (!config.Settings.ExpansionMode || !Instance.DangerousTreasures.CanCall())
                {
                    return;
                }

                var boxes = Pool.GetList<StorageContainer>();

                foreach (var x in _containers)
                {
                    if (x.ShortPrefabName == "box.wooden.large")
                    {
                        boxes.Add(x);
                    }
                }

                if (boxes.Count > 0)
                {
                    Instance.DangerousTreasures?.Call("API_SetContainer", boxes.GetRandom(), Radius, !Options.NPC.Enabled || Options.NPC.UseExpansionNpcs);
                }

                Pool.FreeList(ref boxes);
            }

            private bool ToggleNpcMinerHat(ScientistNPC npc, bool state)
            {
                if (npc.IsNull() || npc.inventory == null || npc.IsDead())
                {
                    return false;
                }

                var slot = npc.inventory.FindItemID("hat.miner");

                if (slot == null)
                {
                    return false;
                }

                if (state && slot.contents != null)
                {
                    slot.contents.AddItem(ItemManager.FindItemDefinition("lowgradefuel"), 50);
                }

                slot.SwitchOnOff(state);
                npc.inventory.ServerUpdate(0f);
                return true;
            }

            public void ToggleLights()
            {
                bool state = config.Settings.Management.AlwaysLights || TOD_Sky.Instance?.IsDay == false;

                if (lights?.Count > 0)
                {
                    foreach (var io in lights)
                    {
                        if (io.IsKilled()) continue;
                        io.UpdateHasPower(state ? 25 : 0, 1);
                        io.SetFlag(BaseEntity.Flags.On, state);
                        io.SendNetworkUpdateImmediate();
                    }
                }

                if (ovens?.Count > 0)
                {
                    foreach (var oven in ovens.Where(oven => !oven.IsKilled()))
                    {
                        if (state && (oven.ShortPrefabName.Contains("furnace") && oven is BaseOven && (oven as BaseOven).inventory.IsEmpty())) continue;
                        oven.SetFlag(BaseEntity.Flags.On, state);
                    }
                }

                if (npcs?.Count > 0)
                {
                    foreach (var npc in npcs.Where(npc => !npc.IsKilled()))
                    {
                        ToggleNpcMinerHat(npc, state);
                    }
                }

                lightsOn = state;
            }

            public void Undo()
            {
                if (IsOpened)
                {
                    IsOpened = false;
                    CancelInvoke(ResetOwner);
                    CancelInvoke(Despawn);

                    float time = config.Settings.Management.DespawnMinutes * 60f;

                    if (time > 0f)
                    {
                        despawnTime = Time.time + time;
                        despawnDateTime = DateTime.Now.AddSeconds(time);

                        if (config.EventMessages.ShowWarning)
                        {
                            var grid = FormatGridReference(Location);

                            foreach (var target in BasePlayer.activePlayerList)
                            {
                                QueueNotification(target, "DestroyingBaseAt", grid, config.Settings.Management.DespawnMinutes);
                            }
                        }

                        Invoke(Despawn, time);

                        despawnTimer = MyInstance.timer.Once(time, Despawn);
                    }
                    else
                    {
                        Despawn();
                    }
                }
            }

            public bool Any(ulong userid, bool checkAllies = true)
            {
                if (ownerId == userid) return true;
                Raider ri;
                if (!raiders.TryGetValue(userid, out ri)) return false;
                return ri.IsParticipant || checkAllies && ri.IsAlly;
            }

            public static bool IsOwner(BasePlayer player, bool isLoading)
            {
                return Instance.Raids.Exists(raid => raid.ownerId == player.userID && (raid.IsOpened || raid.IsDespawning || isLoading && raid.IsLoading));
            }

            public static bool Has(ulong userID)
            {
                return Instance.HumanoidBrains.ContainsKey(userID);
            }

            public static bool Has(TriggerBase triggerBase)
            {
                return Instance.Raids.Exists(raid => raid.triggers.ContainsKey(triggerBase));
            }

            public static bool Has(BaseEntity entity)
            {
                return entity.IsValid() && Instance.RaidEntities.ContainsKey(entity.net.ID);
            }

            public static int Get(RaidableType type)
            {
                int sum = 0;
                foreach (var sp in Instance.Queues.queue)
                {
                    if (sp.type == type)
                    {
                        sum++;
                    }
                }
                foreach (var raid in Instance.Raids)
                {
                    if (raid.Type == type)
                    {
                        sum++;
                    }
                }
                return sum;
            }

            public static int Get()
            {
                return Instance.Queues.queue.Count + Instance.Raids.Count;
            }

            public static RaidableBase Get(ulong userID)
            {
                HumanoidBrain brain;
                return Instance.HumanoidBrains.TryGetValue(userID, out brain) ? brain.raid : null;
            }

            public static RaidableBase Get(Vector3 target, float f = 0f)
            {
                return Instance.Raids.FirstOrDefault(raid => InRange2D(raid.Location, target, raid.ProtectionRadius + f));
            }

            public static RaidableBase Get(BaseEntity a, BaseEntity b)
            {
                return Get(a.transform.position) ?? Get(b.transform.position);
            }

            public static RaidableBase Get(BasePlayer victim, HitInfo hitInfo = null)
            {
                if (Has(victim.userID))
                {
                    return Get(victim.userID);
                }
                DelaySettings ds;
                if (Instance.PvpDelay.TryGetValue(victim.userID, out ds) && ds.RaidableBase != null)
                {
                    return ds.RaidableBase;
                }
                return Get(victim.ServerPosition) ?? Get(hitInfo);
            }

            public static RaidableBase Get(HitInfo hitInfo)
            {
                if (hitInfo != null)
                {
                    if (!hitInfo.Initiator.IsKilled())
                    {
                        var raid = Get(hitInfo.Initiator.ServerPosition);
                        if (raid != null) return raid;
                    }
                    if (!hitInfo.WeaponPrefab.IsKilled())
                    {
                        var raid = Get(hitInfo.WeaponPrefab.ServerPosition);
                        if (raid != null) return raid;
                    }
                    if (!hitInfo.Weapon.IsKilled())
                    {
                        return Get(hitInfo.Weapon.ServerPosition);
                    }
                }
                return null;
            }

            public static RaidableBase Get(PlayerCorpse corpse)
            {
                if (!corpse.playerSteamID.IsSteamId())
                {
                    return Get(corpse.playerSteamID);
                }

                DelaySettings ds;
                return Instance.PvpDelay.TryGetValue(corpse.playerSteamID, out ds) ? ds.RaidableBase : Get(corpse.transform.position);
            }

            public static RaidableBase Get(BaseEntity entity, RaidableBases instance)
            {
                if (!entity.IsValid())
                {
                    return null;
                }
                RaidEntity re;
                return instance.RaidEntities.TryGetValue(entity.net.ID, out re) ? re.raid : null;
            }

            public static bool IsTooClose(Vector3 target, float radius)
            {
                for (int i = 0; i < Instance.Raids.Count; i++)
                {
                    if (InRange2D(Instance.Raids[i].Location, target, radius))
                    {
                        return true;
                    }
                }
                return false;
            }

            private static bool IsBlacklistedSkin(ItemDefinition def, int num)
            {
                var skinId = ItemDefinition.FindSkin(def.isRedirectOf?.itemid ?? def.itemid, num);
                var dirSkin = def.isRedirectOf == null ? def.skins.FirstOrDefault(x => (ulong)x.id == skinId) : def.isRedirectOf.skins.FirstOrDefault(x => (ulong)x.id == skinId);
                var itemSkin = (dirSkin.id == 0) ? null : (dirSkin.invItem as ItemSkin);

                return itemSkin?.Redirect != null || def.isRedirectOf != null;
            }

            public ulong GetItemSkin(ItemDefinition def, ulong defaultSkin, bool unique)
            {
                ulong skin = defaultSkin;

                if (def.shortname != "explosive.satchel" && def.shortname != "grenade.f1")
                {
                    if (!skins.TryGetValue(def.shortname, out skin)) // apply same skin once randomly chosen so items with skins can stack properly
                    {
                        skin = defaultSkin;
                    }

                    if (!unique || skin == 0)
                    {
                        var si = GetItemSkins(def);
                        var random = new List<ulong>();

                        if (config.Skins.Loot.RandomWorkshopSkins && si.workshopSkins.Count > 0)
                        {
                            random.Add(si.workshopSkins.GetRandom());
                        }

                        if (config.Skins.Loot.Imported && si.importedSkins.Count > 0)
                        {
                            random.Add(si.importedSkins.GetRandom());
                        }

                        if (config.Skins.Loot.RandomSkins && si.skins.Count > 0)
                        {
                            random.Add(si.skins.GetRandom());
                        }

                        if (random.Count != 0)
                        {
                            skins[def.shortname] = skin = random.GetRandom();
                        }
                    }
                }

                return skin;
            }

            public static SkinInfo GetItemSkins(ItemDefinition def)
            {
                SkinInfo si;
                if (!Instance.Skins.TryGetValue(def.shortname, out si))
                {
                    Instance.Skins[def.shortname] = si = new SkinInfo();

                    foreach (var skin in def.skins)
                    {
                        if (IsBlacklistedSkin(def, skin.id))
                        {
                            continue;
                        }

                        var id = Convert.ToUInt64(skin.id);

                        si.skins.Add(id);
                        si.allSkins.Add(id);
                    }

                    if (config.Skins.Loot.Imported)
                    {
                        List<ulong> value;
                        if (Instance.ImportedWorkshopSkins.SkinList.TryGetValue(def.shortname, out value))
                        {
                            foreach (var skin in value)
                            {
                                if (IsBlacklistedSkin(def, (int)skin))
                                {
                                    continue;
                                }

                                si.allSkins.Add(skin);
                                si.importedSkins.Add(skin);
                            }
                        }
                    }

                    if (def.skins2 == null)
                    {
                        return si;
                    }

                    foreach (var skin in def.skins2)
                    {
                        if (IsBlacklistedSkin(def, (int)skin.WorkshopId))
                        {
                            continue;
                        }

                        if (!si.workshopSkins.Contains(skin.WorkshopId))
                        {
                            si.workshopSkins.Add(skin.WorkshopId);
                            si.allSkins.Add(skin.WorkshopId);
                        }
                    }
                }

                return si;
            }

            public bool IsAlly(ulong playerId, ulong targetId, AlliedType type = AlliedType.All)
            {
                if (type == AlliedType.All || type == AlliedType.Team)
                {
                    RelationshipManager.PlayerTeam team;
                    if (RelationshipManager.ServerInstance.playerToTeam.TryGetValue(playerId, out team) && team.members.Contains(targetId))
                    {
                        return true;
                    }
                }

                if ((type == AlliedType.All || type == AlliedType.Clan) && Convert.ToBoolean(Instance.Clans?.Call("IsMemberOrAlly", playerId.ToString(), targetId.ToString())))
                {
                    return true;
                }

                if ((type == AlliedType.All || type == AlliedType.Friend) && Convert.ToBoolean(Instance.Friends?.Call("AreFriends", playerId.ToString(), targetId.ToString())))
                {
                    return true;
                }

                return false;
            }

            public bool IsAlly(BasePlayer player)
            {
                if (!ownerId.IsSteamId() || CanBypass(player) || player.userID == ownerId)
                {
                    return true;
                }

                Raider ri = GetRaider(player);

                if (ri.IsAlly || IsAlly(player.userID, ownerId))
                {
                    ri.IsAlly = true;
                    return true;
                }

                return false;
            }

            public static void StopUsingWeapon(BasePlayer player)
            {
                if (player.svActiveItemID.Value == 0)
                {
                    return;
                }

                if (config.Settings.NoWizardry && Instance.Wizardry.CanCall())
                {
                    StopUsingWeapon(player, "knife.bone");
                }

                if (config.Settings.NoArchery && Instance.Archery.CanCall())
                {
                    StopUsingWeapon(player, "bow.compound", "bow.hunting", "crossbow");
                }
            }

            public static void StopUsingWeapon(BasePlayer player, params string[] weapons)
            {
                Item item = player.GetActiveItem();

                if (item == null || !weapons.Contains(item.info.shortname))
                {
                    return;
                }

                if (!item.MoveToContainer(player.inventory.containerMain))
                {
                    item.DropAndTossUpwards(player.GetDropPosition() + player.transform.forward, 2f);
                    Message(player, "TooPowerfulDrop");
                }
                else Message(player, "TooPowerful");
            }

            public BackpackData AddBackpack(DroppedItemContainer backpack, BasePlayer player)
            {
                BackpackData data;
                if (!backpacks.TryGetValue(backpack.net.ID, out data))
                {
                    backpacks[backpack.net.ID] = data = new BackpackData
                    {
                        backpack = backpack,
                        _player = player,
                        userID = backpack.playerSteamID
                    };
                }

                return data;
            }

            private void RemoveParentFromEntitiesOnElevators()
            {
                foreach (var e in FindEntitiesOfType<BaseEntity>(Location, ProtectionRadius))
                {
                    if ((e is PlayerCorpse || e is DroppedItemContainer) && e.HasParent())
                    {
                        e.SetParent(null, false, true);
                    }
                }
            }

            public bool EjectBackpack(NetworkableId nid, BackpackData data, bool bypass)
            {
                if (data.backpack.IsKilled())
                {
                    return true;
                }

                if (!bypass && (!ownerId.IsSteamId() || Any(data.userID) || data.player.IsReallyValid() && IsAlly(data.player)))
                {
                    return false;
                }

                var position = GetEjectLocation(data.backpack.transform.position, 5f, Location, ProtectionRadius);

                position.y = Mathf.Max(position.y, TerrainMeta.WaterMap.GetHeight(position));
                data.backpack.transform.position = position;
                data.backpack.TransformChanged();

                var player = data.player;

                if (player.IsReallyConnected())
                {
                    EjectionNotice(player);

                    if (config.Settings.Management.DrawTime > 0)
                    {
                        AdminCommand(player, () => DrawText(player, config.Settings.Management.DrawTime, Color.red, data.backpack.transform.position, mx("YourCorpse", player.UserIDString)));
                    }
                }

                Interface.CallHook("OnRaidableBaseBackpackEjected", new object[] { data.player, data.userID, data.backpack, Location, AllowPVP, 512, GetOwner(), GetRaiders(), BaseName });

                return true;
            }

            private static void EjectionNotice(BasePlayer player)
            {
                if (!player.IsReallyConnected())
                {
                    return;
                }
                if (player.IsDead() || player.IsSleeping())
                {
                    player.Invoke(() => EjectionNotice(player), 1f);
                    return;
                }
                QueueNotification(player, "EjectedYourCorpse");
            }

            private void EjectSleepers()
            {
                if (config.Settings.Management.EjectSleepers)
                {
                    foreach (var player in FindEntitiesOfType<BasePlayer>(Location, ProtectionRadius, Layers.Mask.Player_Server))
                    {
                        if (player.IsSleeping() && !player.IsBuildingAuthed())
                        {
                            RemovePlayer(player, Location, ProtectionRadius, Type);
                        }
                    }
                }
            }

            public static Vector3 GetEjectLocation(Vector3 a, float distance, Vector3 target, float radius)
            {
                var position = ((a.XZ3D() - target.XZ3D()).normalized * (radius + distance)) + target; // credits ZoneManager
                float y = TerrainMeta.HighestPoint.y + 250f;

                RaycastHit hit;
                if (Physics.Raycast(position + new Vector3(0f, y, 0f), Vector3.down, out hit, Mathf.Infinity, targetMask2, QueryTriggerInteraction.Ignore))
                {
                    position.y = hit.point.y + 0.75f;
                }
                else position.y = Mathf.Max(TerrainMeta.HeightMap.GetHeight(position), TerrainMeta.WaterMap.GetHeight(position)) + 0.75f;

                return position;
            }

            public static bool RemovePlayer(BasePlayer player, Vector3 a, float radius, RaidableType type, bool isJetpack = false)
            {
                if (player.IsNull() || !player.IsHuman())
                {
                    return false;
                }

                if (!isJetpack && !IsWearingJetpack(player))
                {
                    var m = player.GetMounted();

                    if (m.IsReallyValid())
                    {
                        var players = GetMountedPlayers(m);

                        players.RemoveAll(x => x.IsNull() || !x.IsHuman());

                        return EjectMountable(m, players, a, radius);
                    }
                }
                else Interface.CallHook("RemoveJetPack", player.userID);

                var position = GetEjectLocation(player.transform.position, 10f, a, radius);

                if (player.IsFlying)
                {
                    position.y = player.transform.position.y;
                }

                player.Teleport(position);
                player.SendNetworkUpdateImmediate();

                return true;
            }

            public void DismountAllPlayers(BaseMountable m)
            {
                foreach (var target in GetMountedPlayers(m))
                {
                    if (target.IsNull()) continue;

                    m.DismountPlayer(target, false);

                    target.EnsureDismounted();
                }
            }

            public static List<BasePlayer> GetMountedPlayers(HotAirBalloon m)
            {
                var players = FindEntitiesOfType<BasePlayer>(m.CenterPoint(), 1.75f, Layers.Mask.Player_Server);
                players.RemoveAll(player => !player.IsHuman() || !(player.GetParentEntity() == m));
                return players;
            }

            public static List<BasePlayer> GetMountedPlayers(BaseMountable m)
            {
                BaseVehicle vehicle = m.HasParent() ? m.VehicleParent() : m as BaseVehicle;

                if (vehicle.IsReallyValid())
                {
                    return GetMountedPlayers(vehicle);
                }

                var players = new List<BasePlayer>();
                var player = m.GetMounted();

                if (player.IsReallyValid() && player.IsHuman())
                {
                    players.Add(player);
                }

                return players;
            }

            private static List<BasePlayer> GetMountedPlayers(BaseVehicle vehicle)
            {
                var players = new List<BasePlayer>();

                if (!vehicle.HasMountPoints())
                {
                    var player = vehicle.GetMounted();

                    if (player?.IsHuman() == true && !players.Contains(player))
                    {
                        players.Add(player);
                    }

                    return players;
                }

                foreach (var mountPoint in vehicle.allMountPoints)
                {
                    var player = mountPoint.mountable?.GetMounted();

                    if (player?.IsHuman() == true && !players.Contains(player))
                    {
                        players.Add(player);
                    }
                }

                return players;
            }

            private bool CanEject(List<BasePlayer> players)
            {
                return players.Exists(player => !intruders.Contains(player.userID) && CanEject(player));
            }

            private bool CanEject(BasePlayer target)
            {
                if (target.IsNull() || target.userID == ownerId)
                {
                    return false;
                }

                if (CannotEnter(target, false))
                {
                    return true;
                }
                else if (CanEject() && !IsAlly(target))
                {
                    TryMessage(target, "OnPlayerEntryRejected");
                    return true;
                }

                return false;
            }

            public bool CanEject()
            {
                if (AllowPVP && Options.EjectLockedPVP && ownerId.IsSteamId())
                {
                    return true;
                }

                if (!AllowPVP && Options.EjectLockedPVE && ownerId.IsSteamId())
                {
                    return true;
                }

                return false;
            }

            private bool CannotEnter(BasePlayer target, bool justEntered)
            {
                if (GetRaider(target).IsAllowed)
                {
                    if (IsBanned(target))
                    {
                        RemovePlayer(target, Location, ProtectionRadius, Type);
                        return true;
                    }
                }
                else if (Exceeds(target) || IsBanned(target) || IsHogging(target) || justEntered && Teleported(target))
                {
                    return RemovePlayer(target, Location, ProtectionRadius, Type);
                }

                return false;
            }

            public bool IsControlledMount(BaseEntity m)
            {
                if (!config.Settings.Management.Mounts.ControlledMounts)
                {
                    return false;
                }

                if (m is BaseChair)
                {
                    DismountAllPlayers(m as BaseMountable);

                    return true;
                }

                var parentEntity = m.GetParentEntity();

                if (parentEntity.IsNull() || parentEntity is RidableHorse)
                {
                    return false;
                }

                if (parentEntity.GetType().Name.Contains("Controller"))
                {
                    DismountAllPlayers(m as BaseMountable);

                    return true;
                }

                return false;
            }

            private bool IsBlockingCampers(ModularCar car)
            {
                if (!config.Settings.Management.Mounts.Campers || car.AttachedModuleEntities == null)
                {
                    return false;
                }

                foreach (var module in car.AttachedModuleEntities)
                {
                    if (module.ShortPrefabName.Contains("module_camper"))
                    {
                        return true;
                    }
                }

                return false;
            }

            private bool TryRemoveMountable(BaseEntity m, List<BasePlayer> players)
            {
                if (m.IsNull() || m.GetParentEntity() is TrainCar || IsControlledMount(m) || Entities.Contains(m))
                {
                    return false;
                }

                bool shouldEject = config.Settings.Management.Mounts.Other;

                if (CanEject(players))
                {
                    shouldEject = true;
                }
                else if (m is BaseBoat)
                {
                    shouldEject = config.Settings.Management.Mounts.Boats;
                }
                else if (m is BasicCar)
                {
                    shouldEject = config.Settings.Management.Mounts.BasicCars;
                }
                else if (m is ModularCar)
                {
                    shouldEject = config.Settings.Management.Mounts.ModularCars || IsBlockingCampers(m as ModularCar);
                }
                else if (m is CH47Helicopter)
                {
                    shouldEject = config.Settings.Management.Mounts.CH47;
                }
                else if (m is RidableHorse)
                {
                    shouldEject = config.Settings.Management.Mounts.Horses;
                }
                else if (m is ScrapTransportHelicopter)
                {
                    shouldEject = config.Settings.Management.Mounts.Scrap;
                }
                else if (m is MiniCopter)
                {
                    shouldEject = config.Settings.Management.Mounts.MiniCopters;
                }
                else if (m is Snowmobile)
                {
                    shouldEject = config.Settings.Management.Mounts.Snowmobile;
                }
                else if (m is StaticInstrument)
                {
                    shouldEject = config.Settings.Management.Mounts.Pianos;
                }
                else if (m is HotAirBalloon)
                {
                    if (config.Settings.Management.Mounts.HotAirBalloon)
                    {
                        return EjectMountable(m as HotAirBalloon, players, Location, ProtectionRadius);
                    }
                }

                if (m is BaseMountable)
                {
                    if (m.name == "FlyingCarpet")
                    {
                        shouldEject = config.Settings.Management.Mounts.FlyingCarpet;
                    }
                    if (shouldEject)
                    {
                        return EjectMountable(m as BaseMountable, players, Location, ProtectionRadius);
                    }
                }

                return false;
            }

            private static bool IsWearingJetpack(BasePlayer player)
            {
                if (!player.IsKilled())
                {
                    var m = player.GetMounted();

                    if (m is BaseMountable && (m.ShortPrefabName == "testseat" || m.ShortPrefabName == "standingdriver") && m.GetParentEntity() is DroppedItemContainer)
                    {
                        return true;
                    }
                }
                return false;
            }

            private static void TryPushMountable(BaseVehicle vehicle, Vector3 target)
            {
                if (vehicle is MiniCopter || vehicle is CH47Helicopter || vehicle.name.Contains("modularcar"))
                {
                    var body = vehicle.rigidBody ?? vehicle.GetComponent<Rigidbody>();
                    Vector3 normalized = Vector3.ProjectOnPlane(vehicle.transform.position - target, vehicle.transform.up).normalized;
                    float d2 = body.mass * 4f;
                    body.AddForce(-normalized * d2, ForceMode.Impulse);
                }
                else
                {
                    var e = vehicle.transform.eulerAngles; // credits k1lly0u

                    vehicle.transform.rotation = Quaternion.Euler(e.x, e.y - 180f, e.z);
                    var body = vehicle.rigidBody ?? vehicle.GetComponent<Rigidbody>();
                    if (body != null)
                    {
                        body.velocity *= -1f;
                    }
                }
            }

            private static bool IsFlying(BasePlayer player)
            {
                return !player.IsKilled() && !player.modelState.onground && TerrainMeta.HeightMap.GetHeight(player.transform.position) < player.transform.position.y - 1f;
            }

            private void TryEjectMountable(BaseEntity e)
            {
                if (e is BaseMountable)
                {
                    var m = e as BaseMountable;
                    var players = GetMountedPlayers(m);
                    if (players.Count == 0)
                    {
                        EjectMountable(m, players, Location, ProtectionRadius);
                    }
                }
                else if (e is HotAirBalloon)
                {
                    var hab = e as HotAirBalloon;
                    var players = GetMountedPlayers(hab);
                    if (players.Count == 0)
                    {
                        EjectMountable(hab, players, Location, ProtectionRadius);
                    }
                }
            }

            public static bool EjectMountable(HotAirBalloon m, List<BasePlayer> players, Vector3 position, float radius)
            {
                var j = TerrainMeta.HeightMap.GetHeight(m.transform.position) - m.transform.position.y;
                var target = ((m.transform.position.XZ3D() - position.XZ3D()).normalized * (radius + 10f)) + position;

                target.y = Mathf.Max(m.transform.position.y, SpawnsController.GetSpawnHeight(target)) + 5f;

                m.transform.position = target;

                return true;
            }

            public static bool EjectMountable(BaseMountable m, List<BasePlayer> players, Vector3 position, float radius)
            {
                m = GetParentMountableEntity(m);

                var j = TerrainMeta.HeightMap.GetHeight(m.transform.position) - m.transform.position.y;
                float distance = m is RidableHorse ? 2f : 10f;

                if (j > 5f)
                {
                    distance += j;
                }

                var target = ((m.transform.position.XZ3D() - position.XZ3D()).normalized * (radius + distance)) + position;

                if (m is MiniCopter || m is CH47Helicopter || players.Exists(player => IsFlying(player)))
                {
                    target.y = Mathf.Max(m.transform.position.y, SpawnsController.GetSpawnHeight(target)) + 5f;
                }
                else target.y = SpawnsController.GetSpawnHeight(target) + 0.1f;

                BaseVehicle vehicle = m.HasParent() ? m.VehicleParent() : m as BaseVehicle;

                if (m is RidableHorse || InRange(m.transform.position, position, radius + 1f) || vehicle.IsNull())
                {
                    var parentEntity = m.GetParentEntity();

                    if (parentEntity != null && parentEntity != m)
                    {
                        parentEntity.transform.position = target;
                    }
                    m.transform.position = target;
                }
                else
                {
                    TryPushMountable(vehicle, target);
                }

                return true;
            }

            private static BaseMountable GetParentMountableEntity(BaseMountable m)
            {
                while (m != null && m.HasParent())
                {
                    var parent = m.GetParentEntity() as BaseMountable;
                    if (parent == null) break;
                    m = parent;
                }

                return m;
            }

            public bool CanSetupEntity(BaseEntity e)
            {
                if (e.IsKilled())
                {
                    Entities.Remove(e);
                    return false;
                }

                if (e.net == null)
                {
                    e.net = Net.sv.CreateNetworkable();
                }

                if (e is StaticInstrument)
                {
                    MyInstance.temporaryData.NID.Remove(e.net.ID.Value);
                    Entities.Remove(e);
                    Interface.Oxide.NextTick(e.SafelyKill);
                    return false;
                }

                return true;
            }

            public void TryRespawnNpc(bool isMurderer)
            {
                if ((!IsOpened && !Options.Levels.Level2) || isInvokingRespawnNpc)
                {
                    return;
                }

                if (Options.RespawnRateMin > 0)
                {
                    Invoke(() => RespawnNpcNow(isMurderer), UnityEngine.Random.Range(Options.RespawnRateMin, Options.RespawnRateMax));
                }
                else Invoke(() => RespawnNpcNow(isMurderer), Options.RespawnRateMax);

                isInvokingRespawnNpc = true;
            }

            private void RespawnNpcNow(bool isMurderer)
            {
                isInvokingRespawnNpc = false;

                if (npcs.Count >= npcMaxAmountMurderers + npcMaxAmountScientists)
                {
                    return;
                }

                var npc = SpawnNpc(isMurderer);

                if (npc.IsNull() || npcs.Count >= npcMaxAmountMurderers + npcMaxAmountScientists)
                {
                    return;
                }

                TryRespawnNpc(isMurderer);
            }

            public void SpawnNpcs()
            {
                if (!Options.NPC.Enabled || (Options.NPC.UseExpansionNpcs && config.Settings.ExpansionMode && Instance.DangerousTreasures.CanCall()))
                {
                    return;
                }

                if (npcMaxAmountMurderers > 0)
                {
                    for (int i = 0; i < npcMaxAmountMurderers; i++)
                    {
                        SpawnNpc(true);
                    }
                }

                if (npcMaxAmountScientists > 0)
                {
                    for (int i = 0; i < npcMaxAmountScientists; i++)
                    {
                        SpawnNpc(false);
                    }
                }
            }

            public bool NearFoundation(Vector3 from, float range = 5f)
            {
                return foundations.Exists(to => InRange2D(from, to, range));
            }

            private NavMeshHit _navHit;

            public Vector3 FindPointOnNavmesh(Vector3 target, float radius)
            {
                int tries = 25;

                while (--tries > 0)
                {
                    if (NavMesh.SamplePosition(target, out _navHit, radius, NavMesh.AllAreas))
                    {
                        if (NearFoundation(_navHit.position) || !IsAcceptableWaterDepth(_navHit.position))
                        {
                            continue;
                        }

                        if (TestInsideRock(_navHit.position) || TestInsideObject(_navHit.position) || IsNpcNearSpot(_navHit.position))
                        {
                            continue;
                        }

                        return _navHit.position;
                    }
                }

                return Vector3.zero;
            }

            private bool IsAcceptableWaterDepth(Vector3 position)
            {
                return WaterLevel.GetOverallWaterDepth(position, true, true, null, false) <= config.Settings.Management.WaterDepth;
            }

            private bool TestInsideObject(Vector3 position)
            {
                return GamePhysics.CheckSphere(position, 0.5f, Layers.Mask.Player_Server | Layers.Server.Deployed, QueryTriggerInteraction.Ignore);
            }

            private bool TestClippedInside(Vector3 position, float radius, int mask)
            {
                var colliders = Pool.GetList<Collider>();
                Vis.Colliders<Collider>(position, radius, colliders, mask, QueryTriggerInteraction.Ignore);
                bool isClipped = colliders.Count > 0;
                Pool.FreeList(ref colliders);
                return isClipped;
            }

            private bool TestInsideRock(Vector3 a)
            {
                bool faces = Physics.queriesHitBackfaces;
                Physics.queriesHitBackfaces = true;
                bool flag = IsRockFaceUpwards(a);
                Physics.queriesHitBackfaces = faces;
                return flag || IsRockFaceDownwards(a);
            }

            private RaycastHit _hit;
            private RaycastHit[] hits;

            private bool IsRockFaceDownwards(Vector3 a)
            {
                Vector3 b = a + new Vector3(0f, 30f, 0f);
                Vector3 d = a - b;
                hits = Physics.RaycastAll(b, d, d.magnitude, Layers.World);
                return hits.Exists(hit => IsRock(hit.collider.ObjectName()));
            }

            private bool IsRockFaceUpwards(Vector3 point)
            {
                return Physics.Raycast(point, Vector3.up, out _hit, 30f, Layers.Mask.World | Layers.Mask.Terrain) && ((_hit.collider.IsOnLayer(Layer.Terrain) || IsRock(_hit.collider.ObjectName())));
            }

            private bool IsRockFaceUpwardsSecondary(Vector3 point)
            {
                bool faces = Physics.queriesHitBackfaces;
                Physics.queriesHitBackfaces = true;
                bool isRockFaceUpwards = IsRockFaceUpwards(point);
                Physics.queriesHitBackfaces = faces;
                return isRockFaceUpwards;
            }

            private bool IsRock(string name) => _prefabs.Exists(value => name.Contains(value, CompareOptions.OrdinalIgnoreCase));

            private List<string> _prefabs = new List<string> { "rock", "formation", "cliff" };

            private ScientistNPC InstantiateEntity(Vector3 position, out HumanoidBrain humanoidBrain)
            {
                var prefabName = StringPool.Get(1536035819);
                var prefab = GameManager.server.FindPrefab(prefabName);
                var go = Facepunch.Instantiate.GameObject(prefab, position, Quaternion.identity);

                go.SetActive(false);

                go.name = prefabName;

                ScientistBrain scientistBrain = go.GetComponent<ScientistBrain>();
                ScientistNPC npc = go.GetComponent<ScientistNPC>();

                humanoidBrain = go.AddComponent<HumanoidBrain>();
                humanoidBrain.DestinationOverride = position;
                humanoidBrain.CheckLOS = humanoidBrain.RefreshKnownLOS = true;
                humanoidBrain.SenseRange = Options.NPC.AggressionRange;
                humanoidBrain.softLimitSenseRange = humanoidBrain.SenseRange * 1.25f;
                humanoidBrain.TargetLostRange = humanoidBrain.SenseRange * 1.25f;
                humanoidBrain.Settings = Options.NPC;
                humanoidBrain.UseAIDesign = false;
                humanoidBrain._baseEntity = npc;
                humanoidBrain.raid = this;
                humanoidBrain.npc = npc;

                DestroyImmediate(scientistBrain, true);

                SceneManager.MoveGameObjectToScene(go, Rust.Server.EntityScene);

                go.SetActive(true); //go.AwakeFromInstantiate();

                return npc;
            }

            private Vector3 RandomPosition()
            {
                return RandomWanderPositions(Mathf.Clamp(Options.ArenaWalls.Radius, 20f, ProtectionRadius) * 0.9f).FirstOrDefault();
            }

            private List<Vector3> RandomWanderPositions(float radius)
            {
                var list = new List<Vector3>();

                for (int i = 0; i < 10; i++)
                {
                    var target = GetRandomPoint(radius);
                    var vector = FindPointOnNavmesh(target, radius);

                    if (vector != Vector3.zero)
                    {
                        list.Add(vector);
                    }
                }

                return list;
            }

            private Vector3 GetRandomPoint(float radius)
            {
                var vector = Location + UnityEngine.Random.onUnitSphere * radius;

                if (Options.Setup.ForcedHeight == -1)
                {
                    vector.y = TerrainMeta.HeightMap.GetHeight(vector); //Location.y;
                }

                return vector;
            }

            private ScientistNPC SpawnNpc(bool isMurderer)
            {
                var positions = RandomWanderPositions(ProtectionRadius * 0.9f);

                if (positions.Count == 0)
                {
                    return null;
                }

                var position = RandomPosition();

                if (position == Vector3.zero)
                {
                    return null;
                }

                HumanoidBrain brain;
                ScientistNPC npc = InstantiateEntity(position, out brain);

                if (npc.IsNull())
                {
                    return null;
                }

                npc.skinID = 14922524;
                npc.userID = (ulong)UnityEngine.Random.Range(0, 10000000);
                npc.UserIDString = npc.userID.ToString();
                npc.displayName = Options.NPC.RandomNames.Count > 0 ? Options.NPC.RandomNames.GetRandom() : RandomUsernames.Get(npc.userID);
                brain.displayName = npc.displayName;
                Instance.HumanoidBrains[brain.uid = npc.userID] = brain;

                var loadout = GetLoadout(npc, brain, isMurderer);

                if (loadout.belt.Count > 0 || loadout.main.Count > 0 || loadout.wear.Count > 0)
                {
                    npc.loadouts = new PlayerInventoryProperties[1];
                    npc.loadouts[0] = loadout;
                }
                else npc.loadouts = new PlayerInventoryProperties[0];

                BasePlayer.bots.Add(npc);

                npc.Spawn();

                npc.CancelInvoke(npc.EquipTest);

                npcs.Add(npc);

                SetupNpc(npc, brain, isMurderer, positions);

                return npc;
            }

            public class Loadout
            {
                public List<PlayerInventoryProperties.ItemAmountSkinned> belt = new List<PlayerInventoryProperties.ItemAmountSkinned>();
                public List<PlayerInventoryProperties.ItemAmountSkinned> main = new List<PlayerInventoryProperties.ItemAmountSkinned>();
                public List<PlayerInventoryProperties.ItemAmountSkinned> wear = new List<PlayerInventoryProperties.ItemAmountSkinned>();
            }

            private PlayerInventoryProperties GetLoadout(ScientistNPC npc, HumanoidBrain brain, bool isMurderer)
            {
                var loadout = CreateLoadout(npc, brain, isMurderer);
                var pip = ScriptableObject.CreateInstance<PlayerInventoryProperties>();

                pip.belt = loadout.belt;
                pip.main = loadout.main;
                pip.wear = loadout.wear;

                return pip;
            }

            private Loadout CreateLoadout(ScientistNPC npc, HumanoidBrain brain, bool isMurderer)
            {
                var loadout = new Loadout();

                switch (isMurderer)
                {
                    case true:
                        AddItemAmountSkinned(loadout.wear, Options.NPC.MurdererItems.Boots);
                        AddItemAmountSkinned(loadout.wear, Options.NPC.MurdererItems.Gloves);
                        AddItemAmountSkinned(loadout.wear, Options.NPC.MurdererItems.Helm);
                        AddItemAmountSkinned(loadout.wear, Options.NPC.MurdererItems.Pants);
                        AddItemAmountSkinned(loadout.wear, Options.NPC.MurdererItems.Shirt);
                        AddItemAmountSkinned(loadout.wear, Options.NPC.MurdererItems.Torso);
                        if (!Options.NPC.MurdererItems.Torso.Exists(v => v.Contains("suit")))
                        {
                            AddItemAmountSkinned(loadout.wear, Options.NPC.MurdererItems.Kilts);
                        }
                        AddItemAmountSkinned(loadout.belt, Options.NPC.MurdererItems.Weapon);
                        break;
                    case false:
                        AddItemAmountSkinned(loadout.wear, Options.NPC.ScientistItems.Boots);
                        AddItemAmountSkinned(loadout.wear, Options.NPC.ScientistItems.Gloves);
                        AddItemAmountSkinned(loadout.wear, Options.NPC.ScientistItems.Helm);
                        AddItemAmountSkinned(loadout.wear, Options.NPC.ScientistItems.Pants);
                        AddItemAmountSkinned(loadout.wear, Options.NPC.ScientistItems.Shirt);
                        AddItemAmountSkinned(loadout.wear, Options.NPC.ScientistItems.Torso);
                        if (!Options.NPC.ScientistItems.Torso.Exists(v => v.Contains("suit")))
                        {
                            AddItemAmountSkinned(loadout.wear, Options.NPC.ScientistItems.Kilts);
                        }
                        AddItemAmountSkinned(loadout.belt, Options.NPC.ScientistItems.Weapon);
                        break;
                }

                return loadout;
            }

            private void AddItemAmountSkinned(List<PlayerInventoryProperties.ItemAmountSkinned> source, List<string> shortnames)
            {
                if (shortnames.Count == 0)
                {
                    return;
                }

                string shortname = shortnames.GetRandom();

                if (shortname == "bow.hunting")
                {
                    shortname = "bow.compound";
                }

                ItemDefinition def = ItemManager.FindItemDefinition(shortname);

                if (def == null)
                {
                    Puts("Invalid shortname for npc item in {0}/{1} profile: {2}", ProfileName, BaseName, shortname);
                    return;
                }

                ulong skin = 0uL;
                if (config.Skins.Npcs)
                {
                    skin = GetItemSkin(def, 0uL, config.Skins.UniqueNpcs);
                }

                source.Add(new PlayerInventoryProperties.ItemAmountSkinned
                {
                    amount = 1,
                    itemDef = def,
                    skinOverride = skin,
                    startAmount = 1
                });
            }

            private void SetupNpc(ScientistNPC npc, HumanoidBrain brain, bool isMurderer, List<Vector3> positions)
            {
                if (Options.NPC.DespawnInventory)
                {
                    npc.LootSpawnSlots = new LootContainer.LootSpawnSlot[0];
                }

                npc.CancelInvoke(npc.PlayRadioChatter);
                npc.DeathEffects = new GameObjectRef[0];
                npc.RadioChatterEffects = new GameObjectRef[0];
                npc.radioChatterType = ScientistNPC.RadioChatterType.NONE;
                npc.startHealth = isMurderer ? Options.NPC.MurdererHealth : Options.NPC.ScientistHealth;
                npc.InitializeHealth(npc.startHealth, npc.startHealth);
                npc.Invoke(() => UpdateItems(npc, brain, isMurderer), 0.2f);
                npc.Invoke(() => brain.SetupMovement(positions), 0.3f);
            }

            private void UpdateItems(ScientistNPC npc, HumanoidBrain brain, bool isMurderer)
            {
                brain.isMurderer = isMurderer;

                List<string> kits;
                if (npcKits.TryGetValue(isMurderer ? "murderer" : "scientist", out kits) && kits.Count > 0)
                {
                    string kit = kits.GetRandom();

                    npc.inventory.Strip();

                    Instance.Kits?.Call("GiveKit", npc, kit);
                }

                EquipWeapon(npc, brain);

                if (!ToggleNpcMinerHat(npc, TOD_Sky.Instance?.IsNight == true))
                {
                    npc.inventory.ServerUpdate(0f);
                }
            }

            public void EquipWeapon(ScientistNPC npc, HumanoidBrain brain)
            {
                foreach (Item item in npc.inventory.AllItems())
                {
                    var e = item.GetHeldEntity() as HeldEntity;

                    if (e.IsReallyValid())
                    {
                        MyInstance.temporaryData.NID.Add(e.net.ID.Value);

                        if (item.skin != 0)
                        {
                            e.skinID = item.skin;
                            e.SendNetworkUpdate();
                        }

                        if (!brain.AttackEntity.IsNull() || item.info.shortname == "syringe.medical")
                        {
                            continue;
                        }

                        var weapon = e as BaseProjectile;

                        if (weapon.IsReallyValid())
                        {
                            weapon.primaryMagazine.contents = weapon.primaryMagazine.capacity;
                            weapon.SendNetworkUpdateImmediate();
                        }

                        if (e is AttackEntity && item.GetRootContainer() == npc.inventory.containerBelt)
                        {
                            var attackEntity = e as AttackEntity;

                            if (attackEntity.hostile || item.info.shortname == "syringe.medical")
                            {
                                UpdateWeapon(npc, brain, attackEntity, item);
                            }
                        }
                    }

                    item.MarkDirty();
                }
            }

            private void UpdateWeapon(ScientistNPC npc, HumanoidBrain brain, AttackEntity attackEntity, Item item)
            {
                npc.UpdateActiveItem(item.uid);

                if (attackEntity is Chainsaw)
                {
                    (attackEntity as Chainsaw).ServerNPCStart();
                }

                npc.damageScale = 1f;

                attackEntity.TopUpAmmo();
                attackEntity.SetHeld(true);
                brain.Init();
            }

            private bool IsOutside(BaseEntity entity)
            {
                OBB oBB = entity.WorldSpaceBounds();

                return entity.IsOutside(oBB.position.WithY(entity.transform.position.y));
            }

            private bool IsNpcNearSpot(Vector3 position)
            {
                return npcs.Exists(npc => !npc.IsKilled() && InRange(npc.transform.position, position, 0.5f));
            }

            private void SetupNpcKits()
            {
                var murdererKits = new List<string>();
                var scientistKits = new List<string>();

                foreach (string kit in Options.NPC.MurdererKits)
                {
                    if (Convert.ToBoolean(Instance.Kits?.Call("isKit", kit)))
                    {
                        murdererKits.Add(kit);
                    }
                }

                foreach (string kit in Options.NPC.ScientistKits)
                {
                    if (Convert.ToBoolean(Instance.Kits?.Call("isKit", kit)))
                    {
                        scientistKits.Add(kit);
                    }
                }

                npcKits = new Dictionary<string, List<string>>
                {
                    { "murderer", murdererKits },
                    { "scientist", scientistKits }
                };
            }

            public void UpdateMarker()
            {
                if (IsLoading)
                {
                    Invoke(UpdateMarker, 1f);
                    return;
                }

                if (!genericMarker.IsKilled())
                {
                    genericMarker.SendUpdate();
                }

                if (!explosionMarker.IsKilled())
                {
                    explosionMarker.transform.position = Location;
                    explosionMarker.SendNetworkUpdate();
                }

                if (!vendingMarker.IsKilled())
                {
                    vendingMarker.transform.position = Location;
                    float seconds = despawnTime - Time.time;
                    string despawnText = config.Settings.Management.DespawnMinutesInactive > 0 && seconds > 0 ? string.Format(" [{0}m]", Math.Floor(TimeSpan.FromSeconds(seconds).TotalMinutes)) : null;
                    string flag = mx(AllowPVP ? "PVPFlag" : "PVEFlag");

                    vendingMarker.markerShopName = (markerName == config.Settings.Markers.MarkerName ? mx("MapMarkerOrderWithMode", null, flag, Mode(), markerName, despawnText) : string.Format("{0} {1}", flag, markerName)).Trim();
                    vendingMarker.SendNetworkUpdate();
                }

                if (markerCreated || !IsMarkerAllowed())
                {
                    return;
                }

                if (config.Settings.Markers.UseExplosionMarker)
                {
                    explosionMarker = GameManager.server.CreateEntity(StringPool.Get(4060989661), Location) as MapMarkerExplosion;

                    if (!explosionMarker.IsNull())
                    {
                        explosionMarker.Spawn();
                        explosionMarker.Invoke(() => explosionMarker.CancelInvoke(explosionMarker.DelayedDestroy), 1f);
                    }
                }
                else if (config.Settings.Markers.UseVendingMarker)
                {
                    vendingMarker = GameManager.server.CreateEntity(StringPool.Get(3459945130), Location) as VendingMachineMapMarker;

                    if (!vendingMarker.IsNull())
                    {
                        string flag = mx(AllowPVP ? "PVPFlag" : "PVEFlag");
                        string despawnText = config.Settings.Management.DespawnMinutesInactive > 0 ? string.Format(" [{0}m]", config.Settings.Management.DespawnMinutesInactive.ToString()) : null;

                        if (markerName == config.Settings.Markers.MarkerName)
                        {
                            vendingMarker.markerShopName = mx("MapMarkerOrderWithMode", null, flag, Mode(), markerName, despawnText);
                        }
                        else vendingMarker.markerShopName = mx("MapMarkerOrderWithoutMode", null, flag, markerName, despawnText);

                        vendingMarker.enabled = false;
                        vendingMarker.Spawn();
                    }
                }

                markerCreated = true;
                UpdateMarker();
            }

            private void CreateGenericMarker()
            {
                if (IsMarkerAllowed() && (config.Settings.Markers.UseExplosionMarker || config.Settings.Markers.UseVendingMarker))
                {
                    genericMarker = GameManager.server.CreateEntity(StringPool.Get(2849728229), Location) as MapMarkerGenericRadius;

                    if (!genericMarker.IsNull())
                    {
                        genericMarker.alpha = 0.75f;
                        genericMarker.color1 = GetMarkerColor1();
                        genericMarker.color2 = GetMarkerColor2();
                        genericMarker.radius = Mathf.Min(2.5f, World.Size <= 3600 ? config.Settings.Markers.SubRadius : config.Settings.Markers.Radius);
                        genericMarker.Spawn();
                        genericMarker.SendUpdate();
                    }
                }
            }

            private bool TryParseHtmlString(string value, out Color color)
            {
                return ColorUtility.TryParseHtmlString(value.StartsWith("#") ? value : $"#{value}", out color);
            }

            private Color GetMarkerColor1()
            {
                Color color;
                return TryParseHtmlString(config.Settings.Management.Colors1.Get(), out color) ? color : Color.green;
            }

            private Color GetMarkerColor2()
            {
                Color color;
                return TryParseHtmlString(config.Settings.Management.Colors2.Get(), out color) ? color : Color.green;
            }

            private bool IsMarkerAllowed()
            {
                if (Options.Silent)
                {
                    return false;
                }

                switch (Type)
                {
                    case RaidableType.Maintained: return config.Settings.Markers.Maintained;
                    case RaidableType.Scheduled: return config.Settings.Markers.Scheduled;
                    default: return config.Settings.Markers.Manual;
                }
            }

            public void CancelInvokes()
            {
                try { CancelInvoke(CheckEntitiesInSphere); } catch { }
                try { CancelInvoke(Protector); } catch { }
            }

            public void DestroyLocks()
            {
                locks.ForEach(SafelyKill);
            }

            public void DestroyNpcs()
            {
                npcs.ForEach(SafelyKill);
            }

            public void DestroySpheres()
            {
                spheres.ForEach(SafelyKill);
            }

            public void DestroyMapMarkers()
            {
                if (!explosionMarker.IsKilled())
                {
                    explosionMarker.CancelInvoke(explosionMarker.DelayedDestroy);
                    explosionMarker.Kill();
                }

                genericMarker.SafelyKill();
                vendingMarker.SafelyKill();
            }
        }

        public static class SpawnsController
        {
            internal static List<ZoneInfo> managedZones;
            internal static List<string> assets;
            internal static List<string> blockedcolliders;
            internal static List<string> _materialNames;
            internal static List<MonumentInfoEx> Monuments = new List<MonumentInfoEx>();

            public class MonumentInfoEx
            {
                public float radius;
                public string text;
                public Vector3 position;
                public MonumentInfoEx(string text, Vector3 position, float radius)
                {
                    this.text = text;
                    this.position = position;
                    this.radius = radius;
                }
            }

            public static void Initialize()
            {
                managedZones = new List<ZoneInfo>();
                _materialNames = new List<string> { "Generic (Instance)", "Concrete (Instance)", "Rock (Instance)", "Metal (Instance)", "Snow (Instance)" };
                assets = new List<string> { "perimeter_wall", "/props/", "/structures/", "/building/", "train_", "powerline_", "dune", "candy-cane", "assets/content/nature/", "assets/content/vehicles", "walkway", "invisible_collider", "train_track", "module_", "junkpile" };
                blockedcolliders = new List<string> { "powerline", "invisible", "TopCol", "swamp_", "floating_" };
                blockedcolliders.AddRange(config.Settings.Management.AdditionalBlockedColliders);
            }

            public static void Clear()
            {
                assets.Clear();
                Monuments.Clear();
                managedZones.Clear();
                _materialNames.Clear();
                blockedcolliders.Clear();
            }

            public static IEnumerator SetupMonuments()
            {
                int attempts = 0;
                while (TerrainMeta.Path == null || TerrainMeta.Path.Monuments == null || TerrainMeta.Path.Monuments.Count == 0)
                {
                    if (++attempts >= 30)
                    {
                        break;
                    }
                    yield return CoroutineEx.waitForSeconds(1f);
                }
                Monuments = new List<MonumentInfoEx>();
                foreach (var prefab in World.Serialization.world.prefabs)
                {
                    if (prefab.id == 1724395471 && prefab.category != "IGNORE_MONUMENT")
                    {
                        yield return CalculateMonumentSize(new Vector3(prefab.position.x, prefab.position.y, prefab.position.z), prefab.category);
                    }
                }
                if (TerrainMeta.Path == null || TerrainMeta.Path.Monuments == null || TerrainMeta.Path.Monuments.Count == 0)
                {
                    yield break;
                }
                foreach (var monument in TerrainMeta.Path.Monuments)
                {
                    if (monument.name.Contains("monument_marker"))
                    {
                        continue;
                    }
                    if (monument.Bounds.size.Max() > 0f)
                    {
                        Monuments.Add(new MonumentInfoEx(monument.displayPhrase.english.Trim(), monument.transform.position, monument.Bounds.size.Max()));
                        continue;
                    }
                    yield return CalculateMonumentSize(monument.transform.position, string.IsNullOrEmpty(monument.displayPhrase.english.Trim()) ? monument.name.Contains("cave") ? "Cave" : monument.name : monument.displayPhrase.english.Trim());
                }
            }

            public static IEnumerator CalculateMonumentSize(Vector3 from, string text)
            {
                int checks = 0;
                float radius = 15f;
                while (radius < World.Size / 2f)
                {
                    int pointsOfTopology = 0;
                    foreach (var to in GetCircumferencePositions(from, radius, 30f, false, false, 0f))
                    {
                        if (SpawnsController.ContainsTopology(TerrainTopology.Enum.Building | TerrainTopology.Enum.Monument, to, 5f))
                        {
                            pointsOfTopology++;
                        }
                        if (++checks >= 25)
                        {
                            yield return CoroutineEx.waitForSeconds(0.0025f);
                            checks = 0;
                        }
                    }
                    if (pointsOfTopology < 4)
                    {
                        break;
                    }
                    radius += 15f;
                }
                Monuments.Add(new MonumentInfoEx(text, from, radius));
            }

            public static List<Vector3> GetCircumferencePositions(Vector3 center, float radius, float next, bool spawnHeight = true, bool shouldSkipSmallRock = false, float y = 0f)
            {
                float degree = 0f;
                float angleInRadians = 2f * Mathf.PI;
                List<Vector3> positions = new List<Vector3>();

                while (degree < 360)
                {
                    float radian = (angleInRadians / 360) * degree;
                    float x = center.x + radius * Mathf.Cos(radian);
                    float z = center.z + radius * Mathf.Sin(radian);
                    Vector3 a = new Vector3(x, y, z);

                    positions.Add(y == 0f ? a.WithY(spawnHeight ? GetSpawnHeight(a, true, shouldSkipSmallRock) : TerrainMeta.HeightMap.GetHeight(a)) : a);

                    degree += next;
                }

                return positions;
            }

            private static bool IsValidMaterial(string materialName) => materialName.Contains("rock_") || _materialNames.Contains(materialName);

            private static bool ShouldSkipSmallRock(RaycastHit hit, string colName)
            {
                return colName.Contains("rock_") || colName.Contains("formation_", CompareOptions.OrdinalIgnoreCase) ? hit.collider.bounds.size.y <= 2f : false;
            }

            //TransformUtil.GetGroundInfo
            public static float GetSpawnHeight(Vector3 target, bool flag = true, bool shouldSkipSmallRock = false, int mask = targetMask)
            {
                float y = TerrainMeta.HeightMap.GetHeight(target);
                float w = TerrainMeta.WaterMap.GetHeight(target);
                float p = TerrainMeta.HighestPoint.y + 250f;
                RaycastHit[] hits = Physics.RaycastAll(target.WithY(p), Vector3.down, ++p, mask, QueryTriggerInteraction.Ignore);
                GamePhysics.Sort(hits);
                for (int i = 0; i < hits.Length; i++)
                {
                    RaycastHit hit = hits[i];
                    string colName = hit.collider.ObjectName();
                    if (shouldSkipSmallRock && i != hits.Length - 1 && ShouldSkipSmallRock(hit, colName))
                    {
                        continue;
                    }
                    if (!IsValidMaterial(hit.collider.MaterialName()) || colName.Contains("sentry"))
                    {
                        continue;
                    }
                    if (config.Settings.Management.AdditionalBlockedColliders.Exists(colName.Contains))
                    {
                        continue;
                    }
                    y = Mathf.Max(y, hit.point.y);
                    break;
                }

                return flag ? Mathf.Max(y, w) : y;
            }

            public static LandLevel GetLandLevel(Vector3 from, float radius, BasePlayer player = null)
            {
                float maxY = -1000;
                float minY = 1000;

                foreach (var to in GetCircumferencePositions(from, radius, 30f, true, true, 0f))
                {
                    if (player != null && player.IsAdmin)
                    {
                        DrawText(player, 30f, Color.blue, to, $"{Mathf.Abs(from.y - to.y):N1}");
                        DrawLine(player, 30f, Color.blue, from, to);
                    }
                    if (to.y > maxY) maxY = to.y;
                    if (to.y < minY) minY = to.y;
                }

                return new LandLevel
                {
                    Min = minY,
                    Max = maxY
                };
            }

            public static bool ContainsTopology(TerrainTopology.Enum mask, Vector3 position, float radius)
            {
                return (TerrainMeta.TopologyMap.GetTopology(position, radius) & (int)mask) != 0;
            }

            public static bool IsLocationBlocked(Vector3 vector)
            {
                string grid = PositionToGrid(vector);
                return config.Settings.Management.BlockedGrids.Exists(blockedGrid => grid.Equals(blockedGrid, StringComparison.OrdinalIgnoreCase)) || IsZoneBlocked(vector);

            }

            public static bool IsZoneBlocked(Vector3 vector)
            {
                foreach (var zone in managedZones)
                {
                    if (zone.IsPositionInZone(vector))
                    {
                        return zone.isBlocked;
                    }
                }
                return config.Settings.UseZoneManagerOnly;
            }

            private static bool IsValidLocation(Vector3 vector, float safeRadius, float minProtectionRadius)
            {
                if (IsLocationBlocked(vector))
                {
                    return false;
                }

                CacheType cacheType;
                if (!IsAreaSafe(vector, safeRadius, safeRadius, Layers.Mask.World | Layers.Mask.Deployed | Layers.Mask.Trigger, out cacheType))
                {
                    return false;
                }

                if (InDeepWater(vector, false, 5f, 5f))
                {
                    return false;
                }

                if (IsMonumentPosition(vector, config.Settings.Management.MonumentDistance > 0 ? config.Settings.Management.MonumentDistance : minProtectionRadius))
                {
                    return false;
                }

                string topology;
                return TopologyChecks(vector, minProtectionRadius, out topology);
            }

            internal static bool TopologyChecks(Vector3 vector, float radius, out string topology)
            {
                if (!config.Settings.Management.AllowOnBeach && ContainsTopology(TerrainTopology.Enum.Beach | TerrainTopology.Enum.Beachside, vector, radius))
                {
                    topology = "Beach or Beachside";
                    return false;
                }

                if (!config.Settings.Management.AllowInland && !ContainsTopology(TerrainTopology.Enum.Beach | TerrainTopology.Enum.Beachside, vector, radius))
                {
                    topology = "Inland";
                    return false;
                }

                if (!config.Settings.Management.AllowOnRailroads && ContainsTopology(TerrainTopology.Enum.Rail | TerrainTopology.Enum.Railside, vector, radius) || HasPointOnRail(vector))
                {
                    topology = "Rail or Railside";
                    return false;
                }

                if (!config.Settings.Management.AllowOnBuildingTopology && ContainsTopology(TerrainTopology.Enum.Building, vector, radius))
                {
                    topology = "Building";
                    return false;
                }

                if (!config.Settings.Management.AllowOnRivers && ContainsTopology(TerrainTopology.Enum.River | TerrainTopology.Enum.Riverside, vector, radius))
                {
                    topology = "River or Riverside";
                    return false;
                }

                if (!config.Settings.Management.AllowOnRoads && ContainsTopology(TerrainTopology.Enum.Road | TerrainTopology.Enum.Roadside, vector, radius / 2f))
                {
                    topology = "Road or Roadside";
                    return false;
                }

                topology = "";
                return true;
            }

            private static bool HasPointOnRail(Vector3 a)
            {
                if (TerrainMeta.Path?.Rails?.Count > 0)
                {
                    foreach (PathList pathList in TerrainMeta.Path.Rails)
                    {
                        if (pathList?.Path?.Points?.Exists(b => InRange(a, b, M_RADIUS * 2f)) ?? false)
                        {
                            return true;
                        }
                    }
                }
                return false;
            }

            public static bool IsBlockedByMapPrefab(Dictionary<Vector3, float> prefabs, Vector3 position)
            {
                foreach (var prefab in prefabs)
                {
                    if (InRange(prefab.Key, position, prefab.Value))
                    {
                        return true;
                    }
                }
                return false;
            }

            public static void ExtractLocation(RaidableSpawns spawns, Vector3 position, float maxLandLevel, float minProtectionRadius, float maxProtectionRadius, float maxWaterDepth)
            {
                if (IsValidLocation(position, CELL_SIZE, minProtectionRadius))
                {
                    var landLevel = GetLandLevel(position, 15f);

                    if (IsFlatTerrain(position, landLevel, maxLandLevel))
                    {
                        var rsl = new RaidableSpawnLocation(position)
                        {
                            WaterHeight = TerrainMeta.WaterMap.GetHeight(position),
                            TerrainHeight = TerrainMeta.HeightMap.GetHeight(position),
                            SpawnHeight = GetSpawnHeight(position, false),
                            Radius = maxProtectionRadius,
                            AutoHeight = true
                        };

                        if (rsl.WaterHeight - rsl.SpawnHeight <= maxWaterDepth)
                        {
                            spawns.Spawns.Add(rsl);
                        }
                    }
                }
            }

            public static bool IsSubmerged(BuildingWaterOptions options, RaidableSpawnLocation rsl)
            {
                if (rsl.WaterHeight - rsl.TerrainHeight > options.WaterDepth)
                {
                    if (!options.AllowSubmerged)
                    {
                        return true;
                    }

                    rsl.Location.y = rsl.WaterHeight;
                }

                return !options.AllowSubmerged && options.SubmergedAreaCheck && IsSubmerged(options, rsl, rsl.Radius);
            }

            private static bool IsSubmerged(BuildingWaterOptions options, RaidableSpawnLocation rsl, float radius)
            {
                if (rsl.Surroundings.Count == 0)
                {
                    rsl.Surroundings = GetCircumferencePositions(rsl.Location, radius, 90f, false, false, 1f);
                }

                foreach (var vector in rsl.Surroundings)
                {
                    float w = TerrainMeta.WaterMap.GetHeight(vector);
                    float h = GetSpawnHeight(vector, false); // TerrainMeta.HeightMap.GetHeight(vector);

                    if (w - h > options.WaterDepth)
                    {
                        return true;
                    }
                }

                return false;
            }

            public static bool IsMonumentPosition(Vector3 a, float extra)
            {
                return SpawnsController.Monuments.Exists(mi =>
                {
                    var dist = a.Distance2D(mi.position);
                    var dir = (mi.position - a).normalized;

                    return dist <= mi.radius + a.Distance2D(mi.position + dir * extra) - dist;
                });
            }

            private static bool IsSafeZone(Vector3 a, float extra)
            {
                return TriggerSafeZone.allSafeZones.Exists(triggerSafeZone =>
                {
                    try
                    {
                        return InRange2D(triggerSafeZone.transform.position, a, triggerSafeZone.triggerCollider.bounds.size.Max() + extra);
                    }
                    catch
                    {
                        return InRange2D(triggerSafeZone.transform.position, a, 200f + extra);
                    }
                });
            }

            public static bool IsAreaSafe(Vector3 area, float protectionRadius, float cupboardRadius, int layers, out CacheType cacheType, RaidableType type = RaidableType.None)
            {
                if (IsSafeZone(area, config.Settings.Management.MonumentDistance))
                {
                    Instance.Queues.Messages.Add("Safe Zone", area);
                    cacheType = CacheType.Delete;
                    return false;
                }

                cacheType = CacheType.Generic;

                int hits = Physics.OverlapSphereNonAlloc(area, Mathf.Max(protectionRadius, cupboardRadius), Vis.colBuffer, layers, QueryTriggerInteraction.Collide);

                for (int i = 0; i < hits; i++)
                {
                    if (cacheType != CacheType.Generic)
                    {
                        goto next;
                    }

                    var collider = Vis.colBuffer[i];
                    var colName = collider.ObjectName();
                    var position = collider.GetPosition();

                    if (position == Vector3.zero || colName == "ZoneManager" || colName.Contains("xmas"))
                    {
                        goto next;
                    }

                    var e = collider.ToBaseEntity();
                    float dist = position.Distance(area);

                    if (e is BuildingPrivlidge)
                    {
                        if (e.OwnerID.IsSteamId() && dist <= cupboardRadius || !e.OwnerID.IsSteamId() && dist <= protectionRadius)
                        {
                            Instance.Queues.Messages.Add($"Blocked by a building privilege", position);
                            cacheType = CacheType.Privilege;
                        }
                        goto next;
                    }

                    string entityName = e.ObjectName();

                    if (assets.Exists(colName.Contains) && (e.IsNull() || entityName.Contains("/treessource/")))
                    {
                        Instance.Queues.Messages.Add("Blocked by a map prefab", $"{position} {colName}");
                        cacheType = CacheType.Delete;
                        goto next;
                    }

                    if (dist > protectionRadius)
                    {
                        goto next;
                    }

                    if (e.IsReallyValid())
                    {
                        if (e.PrefabName.Contains("xmas") || entityName.StartsWith("assets/prefabs/plants"))
                        {
                            goto next;
                        }

                        bool isSteamId = e.OwnerID.IsSteamId();

                        if (e is BasePlayer)
                        {
                            var player = e as BasePlayer;

                            if (!(!player.IsHuman() || player.IsFlying || config.Settings.Management.EjectSleepers && player.IsSleeping()))
                            {
                                Instance.Queues.Messages.Add("Player is too close", $"{player.displayName} ({player.userID}) {e.transform.position}");
                                cacheType = CacheType.Temporary;
                                goto next;
                            }
                        }
                        else if (isSteamId && e is SleepingBag)
                        {
                            goto next;
                        }
                        else if (isSteamId && config.Settings.Schedule.Skip && type == RaidableType.Scheduled)
                        {
                            goto next;
                        }
                        else if (isSteamId && config.Settings.Maintained.Skip && type == RaidableType.Maintained)
                        {
                            goto next;
                        }
                        else if (RaidableBase.Has(e))
                        {
                            Instance.Queues.Messages.Add("Already occupied by a raidable base", e.transform.position);
                            cacheType = CacheType.Temporary;
                            goto next;
                        }
                        else if (e.IsNpc || e is SleepingBag)
                        {
                            goto next;
                        }
                        else if (e is BaseOven)
                        {
                            if (e.bounds.size.Max() > 1.6f)
                            {
                                Instance.Queues.Messages.Add("An oven is too close", e.transform.position);
                                cacheType = CacheType.Temporary;
                                goto next;
                            }
                        }
                        else if (e is PlayerCorpse)
                        {
                            var corpse = e as PlayerCorpse;

                            if (corpse.playerSteamID == 0 || corpse.playerSteamID.IsSteamId())
                            {
                                Instance.Queues.Messages.Add("A player corpse is too close", e.transform.position);
                                cacheType = CacheType.Temporary;
                                goto next;
                            }
                        }
                        else if (e is DroppedItemContainer && e.ShortPrefabName != "item_drop")
                        {
                            var backpack = e as DroppedItemContainer;

                            if (backpack.playerSteamID == 0 || backpack.playerSteamID.IsSteamId())
                            {
                                Instance.Queues.Messages.Add("A player's backpack is too close", e.transform.position);
                                cacheType = CacheType.Temporary;
                                goto next;
                            }
                        }
                        else if (e.OwnerID == 0)
                        {
                            if (e is BuildingBlock)
                            {
                                Instance.Queues.Messages.Add("A building block is too close", $"{e.ShortPrefabName} {e.transform.position}");
                                cacheType = CacheType.Temporary;
                                goto next;
                            }
                            else if (e is MiningQuarry)
                            {
                                Instance.Queues.Messages.Add("A mining quarry is too close", $"{e.ShortPrefabName} {e.transform.position}");
                                cacheType = CacheType.Delete;
                                goto next;
                            }
                        }
                        else
                        {
                            Instance.Queues.Messages.Add("Blocked by other object", $"{e.ShortPrefabName} {e.transform.position}");
                            cacheType = CacheType.Temporary;
                            goto next;
                        }
                    }
                    else if (collider.gameObject.layer == (int)Layer.World)
                    {
                        if (colName.Contains("rock_") || colName.Contains("formation_", CompareOptions.OrdinalIgnoreCase))
                        {
                            if (collider.bounds.size.y > 2f && dist <= CELL_SIZE)
                            {
                                Instance.Queues.Messages.Add("Rock is too large", position);
                                cacheType = CacheType.Delete;
                                goto next;
                            }
                        }
                        else if (!config.Settings.Management.AllowOnRoads && colName.StartsWith("road_"))
                        {
                            Instance.Queues.Messages.Add("Not allowed on roads", position);
                            cacheType = CacheType.Delete;
                            goto next;
                        }
                        else if (!config.Settings.Management.AllowOnIceSheets && colName.StartsWith("ice_sheet"))
                        {
                            Instance.Queues.Messages.Add("Not allowed on ice sheets", position);
                            cacheType = CacheType.Delete;
                            goto next;
                        }
                    }
                    else if (collider.gameObject.layer == (int)Layer.Water)
                    {
                        if (!config.Settings.Management.AllowOnRivers && colName.StartsWith("River Mesh"))
                        {
                            Instance.Queues.Messages.Add("Not allowed on rivers", position);
                            cacheType = CacheType.Delete;
                            goto next;
                        }
                    }

                next:
                    Vis.colBuffer[i] = null;
                }

                return cacheType == CacheType.Generic;
            }

            public static bool IsFlatTerrain(Vector3 center, LandLevel landLevel, float maxLandLevel)
            {
                return landLevel.Max - landLevel.Min <= maxLandLevel && landLevel.Max - center.y <= maxLandLevel;
            }

            public static bool InDeepWater(Vector3 vector, bool seabed, float minDepth, float maxDepth)
            {
                vector.y = TerrainMeta.HeightMap.GetHeight(vector);

                float waterDepth = WaterLevel.GetWaterDepth(vector, true, true, null);

                if (seabed)
                {
                    return waterDepth >= 0 - minDepth && waterDepth <= 0 - maxDepth;
                }

                return waterDepth > maxDepth;
            }

            public static void SetupZones(Plugin ZoneManager)
            {
                if (!ZoneManager.CanCall())
                {
                    return;
                }

                var zoneIds = ZoneManager?.Call("GetZoneIDs") as string[];

                if (zoneIds == null)
                {
                    return;
                }

                managedZones.Clear();
                config.Settings.Inclusions.RemoveAll(x => string.IsNullOrEmpty(x));

                int allowed = 0, blocked = 0;

                foreach (string zoneId in zoneIds)
                {
                    var zoneLoc = ZoneManager.Call("GetZoneLocation", zoneId);

                    if (!(zoneLoc is Vector3))
                    {
                        continue;
                    }

                    var zoneName = Convert.ToString(ZoneManager.Call("GetZoneName", zoneId));
                    var exists = config.Settings.Inclusions.Exists(zone => zone == "*" || zone == zoneId || !string.IsNullOrEmpty(zoneName) && zoneName.Equals(zone, StringComparison.OrdinalIgnoreCase));
                    var radius = ZoneManager.Call("GetZoneRadius", zoneId);
                    var size = ZoneManager.Call("GetZoneSize", zoneId);
                    bool isBlocked = config.Settings.UseZoneManagerOnly ? !exists : true;

                    if (isBlocked) { blocked++; } else { allowed++; }

                    managedZones.Add(new ZoneInfo(zoneLoc, radius, size, isBlocked));
                }

                Puts(mx("AllowedZones", null, allowed));
                Puts(mx("BlockedZones", null, blocked));
            }

            public static bool IsObstructed(Vector3 from, float radius, float landLevel, float forcedHeight)
            {
                int n = 5;
                float f = radius * 0.2f;
                if (forcedHeight != -1)
                {
                    landLevel += forcedHeight;
                }
                while (n-- > 0)
                {
                    float step = f * n;
                    float next = 360f / step;
                    foreach (var to in GetCircumferencePositions(from, step, next, true, true, 0f))
                    {
                        if (Mathf.Abs((from - to).y) > landLevel)
                        {
                            return true;
                        }
                    }
                }
                return false;
            }
        }

        #region Hooks

        private void UnsubscribeHooks()
        {
            if (IsUnloading)
            {
                return;
            }

            Unsubscribe(nameof(CanBGrade));
            Unsubscribe(nameof(CanDoubleJump));
            Unsubscribe(nameof(OnLifeSupportSavingLife));
            Unsubscribe(nameof(OnRestoreUponDeath));
            Unsubscribe(nameof(OnNpcKits));
            Unsubscribe(nameof(CanTeleport));
            Unsubscribe(nameof(canTeleport));
            Unsubscribe(nameof(canRemove));
            Unsubscribe(nameof(CanEntityBeTargeted));
            Unsubscribe(nameof(CanEntityTrapTrigger));
            Unsubscribe(nameof(CanEntityTakeDamage));
            Unsubscribe(nameof(CanOpenBackpack));
            Unsubscribe(nameof(CanBePenalized));
            Unsubscribe(nameof(OnBaseRepair));
            Unsubscribe(nameof(STCanGainXP));
            Unsubscribe(nameof(OnNeverWear));

            Unsubscribe(nameof(OnMlrsFire));
            Unsubscribe(nameof(OnButtonPress));
            Unsubscribe(nameof(OnElevatorButtonPress));
            Unsubscribe(nameof(OnSamSiteTarget));
            Unsubscribe(nameof(OnPlayerCommand));
            Unsubscribe(nameof(OnServerCommand));
            Unsubscribe(nameof(OnTrapTrigger));
            Unsubscribe(nameof(OnEntityBuilt));
            Unsubscribe(nameof(OnStructureUpgrade));
            Unsubscribe(nameof(OnEntityGroundMissing));
            Unsubscribe(nameof(OnEntityKill));
            Unsubscribe(nameof(OnEntityTakeDamage));
            Unsubscribe(nameof(CanLootEntity));
            Unsubscribe(nameof(OnLootEntityEnd));
            Unsubscribe(nameof(OnEntityDeath));
            Unsubscribe(nameof(CanPickupEntity));
            Unsubscribe(nameof(OnPlayerLand));
            Unsubscribe(nameof(OnPlayerDeath));
            Unsubscribe(nameof(OnPlayerDropActiveItem));
            Unsubscribe(nameof(OnEntityEnter));
            Unsubscribe(nameof(OnNpcDuck));
            Unsubscribe(nameof(OnNpcDestinationSet));
            Unsubscribe(nameof(OnCupboardAuthorize));
            Unsubscribe(nameof(OnActiveItemChanged));
            Unsubscribe(nameof(OnLoseCondition));
            Unsubscribe(nameof(OnFireBallSpread));
            Unsubscribe(nameof(OnFireBallDamage));
            Unsubscribe(nameof(OnCupboardProtectionCalculated));
        }

        private void OnMapMarkerAdded(BasePlayer player, ProtoBuf.MapNote note)
        {
            if (player.IsAlive() && player.HasPermission("raidablebases.mapteleport"))
            {
                float y = GetSpawnHeight(note.worldPosition);
                if (player.IsFlying) y = Mathf.Max(y, player.transform.position.y);
                if (config.Settings.DestroyMarker)
                {
                    player.Teleport(note.worldPosition.WithY(y));
                    player.State.pointsOfInterest?.Remove(note);
                    note.Dispose();
                    player.DirtyPlayerState();
                    player.SendMarkersToClient();
                }
            }
        }

        private void OnNewSave(string filename)
        {
            wiped = true;
            temporaryData.NID.Clear();
        }

        private void Init()
        {
            LoadTemporaryData();
            Instance = this;
            IsUnloading = false;
            _sb = new StringBuilder();
            _sb2 = new StringBuilder();
            Buildings = new BuildingTables();
            RaidableBase.IsSpawnerBusy = true;

            if (config.RankedLadder.Amount > 0)
            {
                permission.RegisterPermission("raidablebases.th", this);
                permission.CreateGroup("raidhunter", "raidhunter", 0);
                permission.GrantGroupPermission("raidhunter", "raidablebases.th", this);
            }

            permission.RegisterPermission("raidablebases.allow", this);
            permission.RegisterPermission("raidablebases.allow.commands", this);
            permission.RegisterPermission("raidablebases.setowner", this);
            permission.RegisterPermission("raidablebases.ladder.exclude", this);
            permission.RegisterPermission("raidablebases.durabilitybypass", this);
            permission.RegisterPermission("raidablebases.ddraw", this);
            permission.RegisterPermission("raidablebases.mapteleport", this);
            permission.RegisterPermission("raidablebases.canbypass", this);
            permission.RegisterPermission("raidablebases.lockoutbypass", this);
            permission.RegisterPermission("raidablebases.blockbypass", this);
            permission.RegisterPermission("raidablebases.banned", this);
            permission.RegisterPermission("raidablebases.vipcooldown", this);
            permission.RegisterPermission("raidablebases.notitle", this);
            permission.RegisterPermission("raidablebases.block.fauxadmin", this);
            permission.RegisterPermission("raidablebases.elevators.bypass.building", this);
            permission.RegisterPermission("raidablebases.elevators.bypass.card", this);
            permission.RegisterPermission("raidablebases.hoggingbypass", this);
            permission.RegisterPermission("raidablebases.block.filenames", this);
            lastSpawnRequestTime = Time.realtimeSinceStartup;
            Unsubscribe(nameof(OnMapMarkerAdded));
            Unsubscribe(nameof(OnPlayerSleepEnded));
            Unsubscribe(nameof(CanBuild));
            UnsubscribeHooks();
            SpawnsController.Initialize();
        }

        private void OnServerShutdown()
        {
            foreach (var raid in Raids.ToList())

            {
                raid.IsShuttingDown = true;
                raid.IsUnloading = true;
            }
            IsShuttingDown = true;
            IsUnloading = true;
        }

        private void Unload()
        {
            RaidableBase.IsSpawnerBusy = true;
            IsUnloading = true;
            SaveData();
            TryInvokeMethod(StopLoadCoroutines);
            TryInvokeMethod(() => SetOnSun(false));
            TryInvokeMethod(StartEntityCleanup);
        }

        private void OnServerInitialized(bool isStartup)
        {
            if (!temporaryData.NID.IsNullOrEmpty())
            {
                var tmp = temporaryData.NID.ToList();
                timer.Once(60f, () => TryInvokeMethod(() => temporaryData.StartCoroutine(tmp)));
            }
            Automated = new AutomatedController(this, config.Settings.Maintained.Enabled, config.Settings.Schedule.Enabled);
            Queues = new QueueController();
            AddCovalenceCommand(config.Settings.EventCommand, nameof(CommandRaidBase));
            AddCovalenceCommand(config.Settings.HunterCommand, nameof(CommandRaidHunter));
            AddCovalenceCommand(config.Settings.ConsoleCommand, nameof(CommandRaidBase));
            AddCovalenceCommand("rb.reloadconfig", nameof(CommandReloadConfig));
            AddCovalenceCommand("rb.config", nameof(CommandConfig), "raidablebases.config");
            AddCovalenceCommand("rb.populate", nameof(CommandPopulate), "raidablebases.config");
            AddCovalenceCommand("rb.toggle", nameof(CommandToggle), "raidablebases.config");
            LoadPlayerData();
            CheckForWipe();
            Initialize();
            OceanLevel = WaterSystem.OceanLevel;
            timer.Repeat(Mathf.Clamp(config.EventMessages.Interval, 1f, 60f), 0, CheckNotifications);
            timer.Repeat(30f, 0, UpdateAllMarkers);
            timer.Repeat(60f, 0, CheckOceanLevel);
            timer.Repeat(300f, 0, SaveData);
            Queues.StartCoroutine();
            setupCopyPasteObstructionRadius = ServerMgr.Instance.StartCoroutine(SetupCopyPasteObstructionRadius());
            Puts("Free version initialized.");
        }

        private void OnSunrise()
        {
            Raids.ToList().ForEach(raid => raid.ToggleLights());
        }

        private void OnSunset()
        {
            Raids.ToList().ForEach(raid => raid.ToggleLights());
        }

        public void LoadTemporaryData()
        {
            try { temporaryData = Interface.Oxide.DataFileSystem.ReadObject<TemporaryData>($"{Name}_UID"); } catch (Exception ex) { Puts(ex.ToString()); }
            if (temporaryData == null) temporaryData = new TemporaryData();
        }

        public void LoadPlayerData()
        {
            try { data = Interface.Oxide.DataFileSystem.ReadObject<StoredData>(Name); } catch (Exception ex) { Puts(ex.ToString()); }
            if (data == null) data = new StoredData();
            if (data.Players == null) data.Players = new Dictionary<string, PlayerInfo>();
        }

        private void SaveData()
        {
            SavePlayerData();
            SaveTemporaryData();
        }

        public void SavePlayerData()
        {
            if (data != null)
            {
                data.Players.RemoveAll((userid, playerInfo) => playerInfo.TotalRaids == 0 || playerInfo.IsExpired());
                Interface.Oxide.DataFileSystem.WriteObject(Name, data);
            }
        }

        private string GetPlayerData() => JsonConvert.SerializeObject(data.Players);

        private void SaveTemporaryData()
        {
            if (temporaryData != null)
            {
                Interface.Oxide.DataFileSystem.WriteObject($"{Name}_UID", temporaryData);
            }
        }

        internal void StartEntityCleanup()
        {
            RaidableBase.IsSpawnerBusy = true;
            var entities = new List<BaseEntity>();
            foreach (var raid in Raids.ToList())
            {
                raid.IsUnloading = true;

                if (!IsShuttingDown)
                {
                    Puts(mx("Destroyed Raid"), $"{PositionToGrid(raid.Location)} {raid.Location}");
                    if (raid.IsOpened) TryInvokeMethod(raid.AwardRaiders);
                    entities.AddRange(raid.Entities);
                }

                raid.Despawn();
            }
            if (entities.Count == 0)
            {
                TryInvokeMethod(RemoveHeldEntities);
                TryInvokeMethod(UnsetStatics);
            }
            else UndoLoop(entities, despawnLimit, UndoMounts, UndoStructures, UndoDeployables);
        }

        private void UnsetStatics()
        {
            SpawnsController.Clear();
            UI.DestroyAll();
            Instance = null;
            config = null;
            data = new StoredData();
            _sb = null;
            _sb2 = null;
            RaidableBasesExtensionMethods.ExtensionMethods.p = null;
        }
        
        private void CheckForWipe()
        {
            if (wiped)
            {
                var raids = new List<int>();

                if (data.Players.Count > 0)
                {
                    if (AssignTreasureHunters())
                    {
                        foreach (var entry in data.Players.ToList())
                        {
                            if (entry.Value.Raids > 0)
                            {
                                raids.Add(entry.Value.Raids);
                            }

                            data.Players[entry.Key].Reset();
                        }
                    }

                    if (raids.Count > 0)
                    {
                        var average = raids.Average();

                        data.Players.RemoveAll((userid, playerInfo) => playerInfo.TotalRaids < average);
                    }
                }

                wiped = false;
                NextTick(SaveData);
            }
        }

        private void Reinitialize()
        {
            Instance.Skins.Clear();

            if (config.Settings.TeleportMarker)
            {
                Subscribe(nameof(OnMapMarkerAdded));
            }
            else Unsubscribe(nameof(OnMapMarkerAdded));

            Subscribe(nameof(OnPlayerSleepEnded));
        }

        private object OnLifeSupportSavingLife(BasePlayer player)
        {
            return EventTerritory(player.transform.position) || HasPVPDelay(player.userID) ? true : (object)null;
        }

        private object CanDoubleJump(BasePlayer player)
        {
            return EventTerritory(player.transform.position) || HasPVPDelay(player.userID) ? true : (object)null;
        }

        private object OnRestoreUponDeath(BasePlayer player)
        {
            var raid = RaidableBase.Get(player.transform.position);

            if (raid == null)
            {
                return null;
            }

            return config.Settings.Management.BlockRestorePVE && !raid.AllowPVP || config.Settings.Management.BlockRestorePVP && raid.AllowPVP ? true : (object)null;
        }

        private object OnNpcKits(ulong targetId)
        {
            return RaidableBase.Get(targetId) == null ? (object)null : true;
        }

        private object CanBGrade(BasePlayer player, int playerGrade, BuildingBlock block, Planner planner)
        {
            return player.IsReallyValid() && (EventTerritory(player.transform.position) || PvpDelay.ContainsKey(player.userID)) ? 0 : (object)null;
        }

        private object canRemove(BasePlayer player)
        {
            return !player.IsFlying && EventTerritory(player.transform.position) ? mx("CannotRemove", player.UserIDString) : null;
        }

        private object canTeleport(BasePlayer player)
        {
            return !player.IsFlying && (EventTerritory(player.transform.position) || PvpDelay.ContainsKey(player.userID)) ? m("CannotTeleport", player.UserIDString) : null;
        }

        private object CanTeleport(BasePlayer player, Vector3 to)
        {
            return !player.IsFlying && (EventTerritory(to) || EventTerritory(player.transform.position) || PvpDelay.ContainsKey(player.userID)) ? m("CannotTeleport", player.UserIDString) : null;
        }

        private BasePlayer GetOwnerPlayer(Item item)
        {
            if (item.parentItem == null)
            {
                return item.GetOwnerPlayer();
            }

            return item.parentItem.GetOwnerPlayer();
        }

        private object OnBaseRepair(BuildingManager.Building building, BasePlayer player)
        {
            return EventTerritory(player.transform.position) ? false : (object)null;
        }

        private object STCanGainXP(BasePlayer player, double amount, string pluginName)
        {
            if (pluginName == Name)
            {
                foreach (var raid in Raids)
                {
                    if (raid.GetRaiders().Contains(player))
                    {
                        return true;
                    }
                }
            }
            return null;
        }

        private object OnRaidingUltimateTargetAcquire(BasePlayer player, Vector3 targetPoint)
        {
            var raid = RaidableBase.Get(targetPoint);
            if (raid == null || raid.Options.MLRS) return null;
            return true;
        }

        private object OnNeverWear(Item item, float amount)
        {
            var player = GetOwnerPlayer(item);

            if (player == null || !player.IsHuman() || player.HasPermission("raidablebases.durabilitybypass"))
            {
                return null;
            }

            var raid = RaidableBase.Get(player.transform.position);

            if (raid == null || !raid.Options.EnforceDurability)
            {
                return null;
            }

            return amount;
        }

        private void OnLoseCondition(Item item, ref float amount)
        {
            if (item == null)
            {
                return;
            }

            var player = GetOwnerPlayer(item);

            if (player.IsNull() || !player.userID.IsSteamId() || player.HasPermission("raidablebases.durabilitybypass"))
            {
                return;
            }

            var raid = RaidableBase.Get(player.transform.position);

            if (raid == null || !raid.Options.EnforceDurability)
            {
                return;
            }

            var uid = item.uid;
            float condition;
            if (!raid.conditions.TryGetValue(uid, out condition))
            {
                raid.conditions[uid] = condition = item.condition;
            }

            float _amount = amount;

            NextTick(() =>
            {
                if (raid == null)
                {
                    return;
                }

                if (item == null || !item.IsValid() || item.isBroken)
                {
                    raid.conditions.Remove(uid);
                    return;
                }

                item.condition = condition - _amount;

                if (item.condition <= 0f && item.condition < condition)
                {
                    item.OnBroken();
                    raid.conditions.Remove(uid);
                }
                else raid.conditions[uid] = item.condition;
            });
        }

        private object OnStructureUpgrade(BuildingBlock block, BasePlayer player, BuildingGrade.Enum grade)
        {
            var raid = RaidableBase.Get(block.transform.position);

            if (raid == null || !raid.Options.BuildingRestrictions.Any())
            {
                return null;
            }

            if (!config.Settings.Management.AllowUpgrade && RaidableBase.Has(block))
            {
                return true;
            }

            switch (grade)
            {
                case BuildingGrade.Enum.Metal: return raid.Options.BuildingRestrictions.Metal ? true : (object)null;
                case BuildingGrade.Enum.Stone: return raid.Options.BuildingRestrictions.Stone ? true : (object)null;
                case BuildingGrade.Enum.TopTier: return raid.Options.BuildingRestrictions.HQM ? true : (object)null;
                case BuildingGrade.Enum.Wood: return raid.Options.BuildingRestrictions.Wooden ? true : (object)null;
            }

            return null;
        }

        private void OnEntityBuilt(Planner planner, GameObject go)
        {
            if (go == null)
            {
                return;
            }

            var e = go.ToBaseEntity();

            if (e.IsNull())
            {
                return;
            }

            var raid = RaidableBase.Get(e.transform.position);

            if (raid == null)
            {
                return;
            }

            var player = planner.GetOwnerPlayer();

            if (player.IsNull())
            {
                return;
            }

            if (raid.Options.BuildingRestrictions.Any() && e is BuildingBlock)
            {
                var block = e as BuildingBlock;
                var grade = block.grade;

                block.Invoke(() =>
                {
                    if (raid == null || block.IsDestroyed)
                    {
                        return;
                    }

                    if (block.grade == grade || OnStructureUpgrade(block, player, block.grade) == null)
                    {
                        AddEntity(e, raid);
                        return;
                    }

                    foreach (var ia in block.BuildCost())
                    {
                        player.GiveItem(ItemManager.Create(ia.itemDef, (int)ia.amount));
                    }

                    block.SafelyKill();
                }, 0.1f);
            }
            else if (!raid.intruders.Contains(player.userID))
            {
                e.Invoke(e.SafelyKill, 0.1f);
            }
            else if ((e.ShortPrefabName == "foundation.triangle" || e.ShortPrefabName == "foundation") && raid.NearFoundation(e.transform.position))
            {
                raid.TryMessage(player, "TooCloseToABuilding");
                e.Invoke(e.SafelyKill, 0.1f);
            }
            else AddEntity(e, raid);
        }

        private void AddEntity(BaseEntity e, RaidableBase raid)
        {
            raid.BuiltList[e] = e.transform.position;
            raid.SetupEntity(e, false);

            if (e.name.Contains("assets/prefabs/deployable/"))
            {
                if (config.Settings.Management.DoNotDestroyDeployables)
                {
                    UnityEngine.Object.Destroy(e.GetComponent<DestroyOnGroundMissing>());
                    UnityEngine.Object.Destroy(e.GetComponent<GroundWatch>());
                }
                else
                {
                    raid.AddEntity(e);
                }
            }
            else if (!config.Settings.Management.DoNotDestroyStructures)
            {
                raid.AddEntity(e);
            }
        }

        private void OnElevatorButtonPress(ElevatorLift e, BasePlayer player, Elevator.Direction Direction, bool FullTravel)
        {
            BMGELEVATOR bmgELEVATOR;
            if (_elevators.TryGetValue(e.GetParentEntity().net.ID, out bmgELEVATOR))
            {
                if (bmgELEVATOR.HasCardPermission(player) && bmgELEVATOR.HasBuildingPermission(player))
                {
                    bmgELEVATOR.GoToFloor(Direction, FullTravel);
                }
            }
        }

        private void OnButtonPress(PressButton button, BasePlayer player)
        {
            if (button.OwnerID == 0 && RaidableBase.Has(button))
            {
                foreach (var e in _elevators)
                {
                    if (e.Value.ValidPosition && Vector3Ex.Distance2D(button.ServerPosition, e.Value.ServerPosition) <= 3f)
                    {
                        e.Value.GoToFloor(Elevator.Direction.Up, false, Mathf.CeilToInt(button.transform.position.y));
                    }
                }
            }
        }

        private bool IsProtectedScientist(BasePlayer player, TriggerBase trigger)
        {
            if (!player.GetType().Name.Contains("CustomScientist", CompareOptions.OrdinalIgnoreCase))
            {
                return false;
            }
            var npc = player as NPCPlayer;
            if (npc == null)
            {
                return false;
            }
            var raid = Raids.FirstOrDefault(y => InRange(y.Location, npc.transform.position, y.ProtectionRadius));
            if (raid == null || !raid.Options.NPC.IgnorePlayerTrapsTurrets || !InRange(raid.Location, npc.spawnPos, raid.ProtectionRadius))
            {
                return false;
            }
            var entity = trigger.GetComponentInParent<BaseEntity>();
            if (entity is AutoTurret && entity.OwnerID == 0)
            {
                var turret = entity as AutoTurret;
                turret.authorizedPlayers.Add(new ProtoBuf.PlayerNameID
                {
                    userid = player.userID,
                    username = player.userID.ToString(),
                });
            }
            if (entity is StorageContainer && !raid.priv.IsKilled())
            {
                raid.priv.authorizedPlayers.Add(new ProtoBuf.PlayerNameID
                {
                    userid = player.userID,
                    username = player.userID.ToString(),
                });
            }
            return true;
        }

        private object OnNpcDuck(ScientistNPC npc) => RaidableBase.Has(npc.userID) ? true : (object)null;

        private object OnNpcDestinationSet(ScientistNPC npc, Vector3 newDestination)
        {
            if (npc.IsNull() || npc.NavAgent == null || !npc.NavAgent.enabled || !npc.NavAgent.isOnNavMesh)
            {
                return true;
            }

            HumanoidBrain brain;
            if (!HumanoidBrains.TryGetValue(npc.userID, out brain) || brain.CanRoam(newDestination))
            {
                return null;
            }

            return true;
        }

        private void OnActiveItemChanged(BasePlayer player, Item oldItem, Item newItem)
        {
            if (!player.IsHuman() || !EventTerritory(player.transform.position))
            {
                return;
            }

            RaidableBase.StopUsingWeapon(player);
        }

        private void OnPlayerSleepEnded(BasePlayer player)
        {
            player.Invoke(() =>
            {
                if (player.IsDestroyed || !player.IsHuman())
                {
                    return;
                }

                DelaySettings ds;
                if (PvpDelay.TryGetValue(player.userID, out ds))
                {
                    if (ds.Timer != null && !ds.Timer.Destroyed)
                    {
                        ds.Timer.Callback.Invoke();
                        ds.Timer.Destroy();
                    }

                    PvpDelay.Remove(player.userID);
                }

                if (config.Settings.Management.AllowTeleport)
                {
                    return;
                }

                var raid = RaidableBase.Get(player.transform.position, 5f);

                if (raid == null)
                {
                    return;
                }

                if (InRange2D(player.transform.position, raid.Location, raid.ProtectionRadius))
                {
                    raid.OnEnterRaid(player);
                }
                else RaidableBase.RemovePlayer(player, raid.Location, raid.ProtectionRadius, raid.Type);
            }, 0.015f);
        }

        private object OnPlayerLand(BasePlayer player, float amount)
        {
            var raid = RaidableBase.Get(player.transform.position);

            return raid == null || !raid.IsDespawning ? (object)null : true;
        }

        private void OnPlayerDeath(BasePlayer player, HitInfo hitInfo)
        {
            var raid = RaidableBase.Get(player, hitInfo);

            if (raid == null)
            {
                return;
            }

            if (!player.IsHuman())
            {
                if (!RaidableBase.Has(player.userID))
                {
                    return;
                }

                if (config.Settings.Management.UseOwners && hitInfo != null && hitInfo.Initiator is BasePlayer)
                {
                    var attacker = hitInfo.Initiator as BasePlayer;

                    if (raid.AddLooter(attacker))
                    {
                        raid.TrySetOwner(attacker, player, hitInfo);
                    }
                }

                if (raid.Options.NPC.DespawnInventory)
                {
                    player.inventory.Strip();
                }

                raid.CheckDespawn();
            }
            else
            {
                if (CanDropPlayerBackpack(player, raid))
                {
                    Backpacks?.Call("API_DropBackpack", player);
                }

                raid.OnPlayerExit(player);
            }
        }

        private object OnPlayerDropActiveItem(BasePlayer player, Item item)
        {
            return EventTerritory(player.transform.position) ? true : (object)null;
        }

        private object OnPlayerCommand(BasePlayer player, string command, string[] args)
        {
            if (!player.IsNull() && !player.HasPermission("raidablebases.allow.commands") && EventTerritory(player.transform.position))
            {
                foreach (var value in config.Settings.BlacklistedCommands)
                {
                    if (command.EndsWith(value, StringComparison.OrdinalIgnoreCase))
                    {
                        Message(player, "CommandNotAllowed");
                        return true;
                    }
                }
            }
            return null;
        }

        private object OnServerCommand(ConsoleSystem.Arg arg)
        {
            return OnPlayerCommand(arg.Player(), arg.cmd.FullName, arg.Args);
        }

        private void OnEntityDeath(BuildingPrivlidge priv, HitInfo hitInfo)
        {
            var raid = RaidableBase.Get(priv, this);

            if (raid == null)
            {
                return;
            }

            if (!raid.IsDespawning && config.Settings.Management.AllowCupboardLoot)
            {
                DropOrRemoveItems(priv, raid);
            }

            if (raid.Options.RequiresCupboardAccess)
            {
                OnCupboardAuthorize(priv, null);
            }

            raid.OnBuildingPrivilegeDestroyed();
        }

        private void OnEntityKill(StorageContainer container)
        {
            if (container is BuildingPrivlidge)
            {
                OnEntityDeath(container as BuildingPrivlidge, null);
            }
            if (container != null)
            {
                EntityHandler(container, null);
            }
        }

        private void OnEntityDeath(StorageContainer container, HitInfo hitInfo) => EntityHandler(container, hitInfo);

        private void OnEntityDeath(StabilityEntity entity, HitInfo hitInfo)
        {
            var raid = RaidableBase.Get(entity.transform.position);

            if (raid == null || raid.IsDespawning)
            {
                return;
            }

            var player = hitInfo?.Initiator as BasePlayer;

            if (!player.IsReallyValid())
            {
                return;
            }

            if (raid.AddLooter(player))
            {
                raid.TrySetOwner(player, entity, hitInfo);
            }

            raid.CheckDespawn();

            if (raid.IsDamaged || entity is SimpleBuildingBlock)
            {
                return;
            }

            raid.IsDamaged = true;
        }

        private object OnEntityGroundMissing(StorageContainer container)
        {
            var raid = RaidableBase.Get(container, this);

            return raid != null && !raid.CanHurtBox(container) ? true : (object)null;
        }

        private void OnEntityDeath(IOEntity io, HitInfo hitInfo)
        {
            if (config.Settings.Management.DropLoot.AutoTurret && io is AutoTurret && io.OwnerID == 0uL)
            {
                DropIOLoot(io, true);
            }
            else if (config.Settings.Management.DropLoot.SamSite && io is SamSite && io.OwnerID == 0uL)
            {
                DropIOLoot(io, false);
            }
        }

        private void DropIOLoot(IOEntity io, bool isAutoTurret)
        {
            var raid = RaidableBase.Get(io, this);

            if (raid == null || !raid.IsOpened || raid.IsDespawning || raid.IsLoading)
            {
                return;
            }

            IItemContainerEntity ice = io as IItemContainerEntity;

            if (ice?.inventory?.itemList?.Count > 0)
            {
                var dropPosition = isAutoTurret && io.transform.up.y == 1f ? io.transform.position.WithY(io.transform.position.y + io.bounds.extents.y) : io.GetDropPosition();
                var prefab = StringPool.Get(raid.Options.BuoyantBox ? 146366564u : 545786656u);
                ice.inventory.Drop(prefab, dropPosition, io.transform.rotation, 0f);
            }

            if (isAutoTurret) raid.turrets.Remove(io as AutoTurret);
            else raid.samsites.Remove(io as SamSite);
        }

        private void EntityHandler(StorageContainer container, HitInfo hitInfo)
        {
            var raid = RaidableBase.Get(container, this);

            if (raid == null || raid.IsDespawning || raid.IsLoading)
            {
                return;
            }

            DropOrRemoveItems(container, raid);

            raid._containers.Remove(container);

            UI.UpdateStatusUI(raid);

            if (IsLootingWeapon(hitInfo))
            {
                var player = raid.GetInitiatorPlayer(hitInfo, container);

                if (player.IsReallyValid())
                {
                    raid.AddLooter(player);
                }
            }

            if (raid.IsOpened && (IsBox(container, true) || container is BuildingPrivlidge))
            {
                raid.TryToEnd();
            }

            if (!Raids.Exists(x => x._containers.Count > 0))
            {
                Unsubscribe(nameof(OnEntityKill));
                Unsubscribe(nameof(OnEntityGroundMissing));
            }
        }

        private static bool IsLootingWeapon(HitInfo hitInfo)
        {
            if (hitInfo == null || hitInfo.damageTypes == null)
            {
                return false;
            }

            return hitInfo.damageTypes.Has(DamageType.Explosion) || hitInfo.damageTypes.Has(DamageType.Heat) || hitInfo.damageTypes.IsMeleeType();
        }

        private void OnCupboardAuthorize(BuildingPrivlidge priv, BasePlayer player)
        {
            foreach (var raid in Raids)
            {
                if (raid.priv == priv && raid.Options.RequiresCupboardAccess && !raid.IsAuthed)
                {
                    raid.IsAuthed = true;

                    if (raid.Options.RequiresCupboardAccess && config.EventMessages.AnnounceRaidUnlock)
                    {
                        foreach (var p in BasePlayer.activePlayerList)
                        {
                            QueueNotification(p, "OnRaidFinished", FormatGridReference(raid.Location));
                        }
                    }

                    break;
                }
            }

            if (!Raids.Exists(raid => !raid.IsAuthed))
            {
                Unsubscribe(nameof(OnCupboardAuthorize));
            }
        }

        private object CanPickupEntity(BasePlayer player, BaseEntity entity)
        {
            var raid = RaidableBase.Get(entity, this);

            if (raid == null)
            {
                return null;
            }

            if (player.IsReallyValid() && !raid.AddLooter(player))
            {
                return false;
            }

            if (raid.IsBlacklisted(entity.ShortPrefabName))
            {
                return false;
            }

            return !raid.Options.AllowPickup && entity.OwnerID == 0 ? false : (object)null;
        }

        private void OnFireBallSpread(FireBall entity, BaseEntity fire)
        {
            if (EventTerritory(fire.transform.position))
            {
                NextTick(fire.SafelyKill);
            }
        }

        private void OnFireBallDamage(FireBall fireBall, BaseCombatEntity target, HitInfo hitInfo)
        {
            if (!fireBall.IsKilled() && hitInfo != null && EventTerritory(fireBall.transform.position) && !(hitInfo.Initiator is BasePlayer) && (hitInfo.Initiator == null || fireBall.creatorEntity is BasePlayer))
            {
                hitInfo.Initiator = fireBall.creatorEntity;
            }
        }

        private object CanMlrsTargetLocation(MLRS mlrs, BasePlayer player)
        {
            var raid = RaidableBase.Get(mlrs.TrueHitPos, 25f);
            return raid == null || raid.Options.MLRS ? (object)null : false;
        }

        private object OnMlrsFire(MLRS mlrs, BasePlayer player)
        {
            var raid = RaidableBase.Get(mlrs.TrueHitPos, 25f);
            if (raid == null || raid.Options.MLRS) return null;
            QueueNotification(player, "MLRS Target Denied");
            return true;
        }

        private void OnEntitySpawned(BaseEntity entity)
        {
            if (entity.IsValid() && temporaryData.NID.Remove(entity.net.ID.Value))
            {
                if (entity.OwnerID.IsSteamId()) return;
                NextTick(entity.SafelyKill);
                return;
            }
            if (Raids.Count == 0 || entity.IsKilled())
            {
                return;
            }
            if (entity is MLRSRocket)
            {
                OnEntitySpawnedHandler(entity as MLRSRocket);
            }
            else if (entity is FireBall)
            {
                OnEntitySpawnedHandler(entity as FireBall);
            }
            else if (entity is DroppedItemContainer)
            {
                OnEntitySpawnedHandler(entity as DroppedItemContainer);
            }
            else if (entity is BaseLock)
            {
                OnEntitySpawnedHandler(entity as BaseLock);
            }
            else if (entity is PlayerCorpse)
            {
                OnEntitySpawnedHandler(entity as PlayerCorpse);
            }
        }

        private void OnEntitySpawnedHandler(MLRSRocket rocket)
        {
            if (rocket.IsNull()) return;
            var systems = FindEntitiesOfType<MLRS>(rocket.transform.position, 15f);
            if (systems.Count == 0) return;
            var raid = RaidableBase.Get(systems[0].TrueHitPos);
            if (raid == null) return;
            var owner = systems[0].rocketOwnerRef.Get(true) as BasePlayer;
            if (owner.IsNull()) return;
            rocket.creatorEntity = raid.Options.MLRS ? owner : null;
            rocket.OwnerID = raid.Options.MLRS ? owner.userID : 0uL;
        }

        private void OnEntitySpawnedHandler(FireBall fire)
        {
            if (config.Settings.Management.PreventFireFromSpreading && fire.ShortPrefabName == "flamethrower_fireball" && EventTerritory(fire.transform.position) && fire.creatorEntity is BasePlayer && !fire.creatorEntity.ToPlayer().userID.IsSteamId())
            {
                NextTick(fire.SafelyKill);
            }
        }

        private void OnEntitySpawnedHandler(DroppedItemContainer backpack)
        {
            if (backpack.IsKilled() || IsUnloading)
            {
                return;
            }

            var raid = RaidableBase.Get(backpack.transform.position);

            if (raid == null)
            {
                return;
            }

            if (backpack.ShortPrefabName == "item_drop" || backpack.ShortPrefabName == "item_drop_buoyant")
            {
                raid.AddNearTime = 1800f;
                return;
            }

            bool backpacks = raid.AllowPVP && config.Settings.Management.BackpacksPVP || !raid.AllowPVP && config.Settings.Management.BackpacksPVE;

            NextTick(() =>
            {
                if (IsUnloading || backpack.IsKilled())
                {
                    return;
                }

                if (backpacks || DelaySettings.CanRemoveOwner(backpack))
                {
                    backpack.playerSteamID = 0;
                }
            });
        }

        private void OnEntitySpawnedHandler(BaseLock entity)
        {
            var raid = RaidableBase.Get(entity.transform.position);

            if (raid == null || raid.IsLoading)
            {
                return;
            }

            var parent = entity.GetParentEntity() as StorageContainer;

            if (parent != null && raid._containers.Contains(parent))
            {
                NextTick(entity.SafelyKill);
            }
        }

        private void OnEntitySpawnedHandler(PlayerCorpse corpse)
        {
            if (corpse.IsNull())
            {
                return;
            }

            var raid = RaidableBase.Get(corpse);

            if (raid == null)
            {
                return;
            }

            if (corpse.playerSteamID.IsSteamId())
            {
                var playerSteamID = corpse.playerSteamID;

                if (raid.Options.EjectBackpacks && !playerSteamID.HasPermission("reviveplayer.use"))
                {
                    if (Interface.CallHook("OnRaidablePlayerCorpseCreate", new object[] { corpse, raid.Location, raid.AllowPVP, 512, raid.GetOwner(), raid.GetRaiders(), raid.BaseName }) != null)
                    {
                        return;
                    }

                    if (corpse.containers.IsNullOrEmpty())
                    {
                        goto done;
                    }

                    var container = GameManager.server.CreateEntity(StringPool.Get(1519640547), corpse.transform.position) as DroppedItemContainer;
                    container.maxItemCount = 48;
                    container.lootPanelName = "generic_resizable";
                    container.playerName = corpse.playerName;
                    container.playerSteamID = corpse.playerSteamID;
                    container.Spawn();

                    if (container.IsKilled())
                    {
                        goto done;
                    }

                    container.TakeFrom(corpse.containers);
                    corpse.SafelyKill();

                    var player = RustCore.FindPlayerById(playerSteamID);
                    var data = raid.AddBackpack(container, player);
                    bool canEjectBackpack = Interface.CallHook("OnRaidableBaseBackpackEject", new object[] { container, raid.Location, raid.AllowPVP, 512, raid.GetOwner(), raid.GetRaiders(), raid.BaseName }) == null;

                    if (canEjectBackpack && raid.EjectBackpack(container.net.ID, data, false))
                    {
                        raid.backpacks.Remove(container.net.ID);
                    }

                    if (config.Settings.Management.PlayersLootableInPVE && !raid.AllowPVP || config.Settings.Management.PlayersLootableInPVP && raid.AllowPVP)
                    {
                        container.playerSteamID = 0;
                    }

                    return;
                }

            done:

                if (config.Settings.Management.PlayersLootableInPVE && !raid.AllowPVP || config.Settings.Management.PlayersLootableInPVP && raid.AllowPVP)
                {
                    corpse.playerSteamID = 0;
                }
            }
            else
            {
                raid.npcs.RemoveAll(npc => npc.IsKilled() || npc.userID == corpse.playerSteamID);

                HumanoidBrain brain;
                if (HumanoidBrains.TryGetValue(corpse.playerSteamID, out brain))
                {
                    if (raid.Options.NPC.DespawnInventory)
                    {
                        corpse.Invoke(corpse.SafelyKill, 30f);
                    }

                    if (raid.Options.RespawnRateMax > 0f)
                    {
                        raid.TryRespawnNpc(brain.isMurderer);
                    }
                    else if (!AnyNpcs())
                    {
                        Unsubscribe(nameof(OnNpcDestinationSet));
                    }

                    corpse.playerName = brain.displayName;
                    UnityEngine.Object.Destroy(brain);
                }
            }
        }

        private object CanBuild(Planner planner, Construction construction, Construction.Target target)
        {
            var raid = RaidableBase.Get(target.entity && target.entity.transform && target.socket ? target.GetWorldPosition() : target.position);

            if (raid == null)
            {
                return null;
            }

            if (!raid.Options.AllowBuildingPriviledges && construction.prefabID == 2476970476) // TC
            {
                Message(target.player, "Cupboards are blocked!");
                return false;
            }
            else if (config.Settings.Management.AllowLadders && construction.prefabID == 2150203378) // LADDER
            {
                if (CanBuildLadders(target.player, raid))
                {
                    Raider ri;
                    if (raid.raiders.TryGetValue(target.player.userID, out ri) && ri.Input != null)
                    {
                        ri.Input.Restart();
                        ri.Input.TryPlace(ConstructionType.Ladder);
                    }
                }
                else
                {
                    Message(target.player, "Ladders are blocked!");
                    return false;
                }
            }
            else if (config.Settings.Management.AllowLadders && construction.fullName.Contains("/barricades/barricade."))
            {
                if (raid.Options.Barricades)
                {
                    Raider ri;
                    if (raid.raiders.TryGetValue(target.player.userID, out ri) && ri.Input != null)
                    {
                        ri.Input.Restart();
                        ri.Input.TryPlace(ConstructionType.Barricade);
                    }
                }
                else
                {
                    Message(target.player, "Barricades are blocked!");
                    return false;
                }
            }
            else if (!config.Settings.Management.AllowBuilding)
            {
                Message(target.player, "Building is blocked!");
                return false;
            }

            return null;
        }

        private bool CanBuildLadders(BasePlayer player, RaidableBase raid)
        {
            if (!config.Settings.Management.AllowLadders) return false;
            if (raid.Options.RequiresCupboardAccessLadders) return raid.CanBuild(player);
            return true;
        }

        private void OnLootEntityEnd(BasePlayer player, StorageContainer container)
        {
            if (player.limitNetworking || container?.inventory == null || container.OwnerID.IsSteamId())
            {
                return;
            }

            var raid = RaidableBase.Get(container, this);

            if (raid == null)
            {
                return;
            }

            raid.IsAnyLooted = true;

            if (IsBox(container, true) || container is BuildingPrivlidge)
            {
                UI.UpdateStatusUI(raid);
            }

            if (raid.Options.DropTimeAfterLooting <= 0 || (raid.Options.DropOnlyBoxesAndPrivileges && !IsBox(container, true) && !(container is BuildingPrivlidge)))
            {
                raid.TryToEnd();
                return;
            }

            if (container.inventory.IsEmpty() && (container.ShortPrefabName == "box.wooden.large" || container.ShortPrefabName == "woodbox_deployed" || container.ShortPrefabName == "coffinstorage"))
            {
                container.Invoke(container.SafelyKill, 0.1f);
            }
            else container.Invoke(() => DropOrRemoveItems(container, raid), raid.Options.DropTimeAfterLooting);

            raid.TryToEnd();
        }

        private object CanLootEntity(BasePlayer player, BaseEntity entity)
        {
            return RaidableBase.Get(entity.transform.position)?.CanLootEntityInternal(player, entity);
        }

        private object CanBePenalized(BasePlayer player)
        {
            var raid = RaidableBase.Get(player);

            if (raid != null &&
                (raid.AllowPVP && !raid.Options.PenalizePVP ||
                !raid.AllowPVP && !raid.Options.PenalizePVE))
            {
                return false;
            }

            return null;
        }

        private void CanOpenBackpack(BasePlayer looter, ulong backpackOwnerID)
        {
            var raid = RaidableBase.Get(looter.transform.position);

            if (raid == null)
            {
                return;
            }

            if (!raid.AllowPVP && !config.Settings.Management.BackpacksOpenPVE || raid.AllowPVP && !config.Settings.Management.BackpacksOpenPVP)
            {
                looter.Invoke(looter.EndLooting, 0.01f);
                QueueNotification(looter, "NotAllowed");
            }
        }

        private bool CanDropPlayerBackpack(BasePlayer player, RaidableBase raid)
        {
            DelaySettings ds;
            if (PvpDelay.TryGetValue(player.userID, out ds) && (ds.AllowPVP && config.Settings.Management.BackpacksPVP || !ds.AllowPVP && config.Settings.Management.BackpacksPVE))
            {
                return true;
            }

            return raid != null && (raid.AllowPVP && config.Settings.Management.BackpacksPVP || !raid.AllowPVP && config.Settings.Management.BackpacksPVE);
        }

        private bool IsPositionInSpace(Vector3 a)
        {
            return Space != null && Convert.ToBoolean(Space?.Call("IsPositionInSpace", a));
        }

        private object OnEntityEnter(TriggerBase trigger, BaseEntity entity)
        {
            if (entity is Drone && RaidableBase.Has(trigger))
            {
                return true;
            }

            var player = entity as BasePlayer;

            if (player.IsNull())
            {
                return null;
            }

            if (RaidableBase.Has(player.userID) && (RaidableBase.Has(trigger) || RaidableBase.Get(player.userID).Options.NPC.IgnorePlayerTrapsTurrets))
            {
                return true;
            }

            if (IsProtectedScientist(player, trigger) || ShouldIgnoreFlyingPlayer(player))
            {
                return true;
            }

            if (IsPVE())
            {
                return null;
            }

            var attacker = GameObjectEx.ToBaseEntity(trigger.gameObject);

            if (attacker == null)
            {
                return null;
            }

            var success = CanEntityBeTargeted(player, attacker);

            return success == null || (bool)success ? (object)null : true;
        }

        private bool ShouldIgnoreFlyingPlayer(BasePlayer player) => config.Settings.Management.IgnoreFlying && player.IsFlying && EventTerritory(player.transform.position);

        private bool IsArmoredTrain(BaseEntity entity) => entity.OwnerID == 0uL && entity is AutoTurret && entity.GetParentEntity() is TrainCar;

        private bool IsSentryTargetingNpc(BasePlayer player, BaseEntity entity) => entity is NPCAutoTurret && !player.userID.IsSteamId();

        private object CanEntityBeTargeted(BasePlayer player, BaseEntity entity)
        {
            if (player.IsNull() || entity.IsNull() || player.limitNetworking || IsPositionInSpace(entity.transform.position) || IsSentryTargetingNpc(player, entity) || IsArmoredTrain(entity))
            {
                return null;
            }

            if (PvpDelay.ContainsKey(player.userID))
            {
                return true;
            }

            var raid = RaidableBase.Get(player, entity);

            if (raid == null)
            {
                return null;
            }

            if (RaidableBase.Has(player.userID))
            {
                return entity.OwnerID.IsSteamId() ? !raid.Options.NPC.IgnorePlayerTrapsTurrets : !raid.Entities.Contains(entity);
            }

            if (player.IsHuman())
            {
                if (raid.AllowPVP)
                {
                    return raid.Entities.Contains(entity) || raid.BuiltList.ContainsKey(entity);
                }

                return raid.Entities.Contains(entity) && !raid.BuiltList.ContainsKey(entity);
            }

            return entity.OwnerID.IsSteamId() ? !raid.Options.NPC.IgnorePlayerTrapsTurrets : !raid.Options.NPC.IgnoreTrapsTurrets;
        }

        private object CanEntityBeTargeted(BaseEntity entity, SamSite ss)
        {
            var raid = RaidableBase.Get(ss.transform.position);

            if (raid != null && !IsPositionInSpace(entity.transform.position) && entity.IsValid())
            {
                if (raid.IsLoading || MountEntities.ContainsKey(entity.net.ID))
                {
                    return false;
                }
                return (entity.transform.position - ss.transform.position).magnitude <= config.Weapons.SamSiteRange;
            }

            return null;
        }

        private object OnSamSiteTarget(SamSite ss, BaseEntity entity)
        {
            var raid = RaidableBase.Get(ss.transform.position);

            if (raid != null && !IsPositionInSpace(entity.transform.position) && entity.IsValid())
            {
                if (raid.IsLoading || MountEntities.ContainsKey(entity.net.ID))
                {
                    return true;
                }
                return InRange(entity.transform.position, ss.transform.position, config.Weapons.SamSiteRange) ? (object)null : true;
            }

            return null;
        }

        private object OnTrapTrigger(BaseTrap trap, GameObject go)
        {
            var player = go.GetComponent<BasePlayer>();
            var success = CanEntityTrapTrigger(trap, player);

            return success is bool && !(bool)success ? true : (object)null;
        }

        private object CanEntityTrapTrigger(BaseTrap trap, BasePlayer player)
        {
            if (player.IsNull() || player.limitNetworking)
            {
                return null;
            }

            if (RaidableBase.Has(player.userID))
            {
                return false;
            }

            return EventTerritory(player.transform.position) ? true : (object)null;
        }

        private void OnCupboardProtectionCalculated(BuildingPrivlidge priv, float cachedProtectedMinutes)
        {
            if (priv.OwnerID == 0 && RaidableBase.Has(priv))
            {
                priv.cachedProtectedMinutes = 1500;
            }
        }

        private object CanEntityTakeDamage(BaseCombatEntity entity, HitInfo hitInfo)
        {
            if (hitInfo == null || hitInfo.damageTypes == null || entity.IsNull() || entity.OwnerID == 1337422)
            {
                return null;
            }

            object success = entity is BasePlayer ? HandlePlayerDamage(entity as BasePlayer, hitInfo) : HandleEntityDamage(entity, hitInfo);

            if (success is bool && !(bool)success)
            {
                NullifyDamage(hitInfo);
                return false;
            }

            return success;
        }

        private void OnEntityTakeDamage(BaseCombatEntity entity, HitInfo hitInfo) => CanEntityTakeDamage(entity, hitInfo);

        private object HandlePlayerDamage(BasePlayer victim, HitInfo hitInfo)
        {
            var raid = RaidableBase.Get(victim, hitInfo);

            if (raid == null || raid.IsDespawning)
            {
                return null;
            }

            if (!raid.Options.MLRS && hitInfo.WeaponPrefab is MLRSRocket)
            {
                return false;
            }

            var weapon = hitInfo.Initiator;

            if (weapon != null && IsHelicopter(hitInfo))
            {
                return true;
            }

            if (victim.skinID == 14922524 && weapon != null && weapon.OwnerID == 0 && RaidableBase.Has(weapon))
            {
                return false;
            }

            if (IsTrueDamage(weapon, raid.IsProtectedWeapon(weapon)))
            {
                return HandleTrueDamage(raid, hitInfo, weapon, victim);
            }

            var attacker = raid.GetInitiatorPlayer(hitInfo, victim);

            if (attacker.IsReallyValid())
            {
                return HandleAttacker(attacker, victim, hitInfo, raid);
            }

            return victim.skinID == 14922524 ? false : (object)null;
        }

        private object HandleTrueDamage(RaidableBase raid, HitInfo hitInfo, BaseEntity weapon, BasePlayer victim)
        {
            if (victim is ScientistNPC && !RaidableBase.Has(victim.userID))
            {
                return null;
            }

            if (weapon is AutoTurret)
            {
                hitInfo.damageTypes.Scale(DamageType.Bullet, UnityEngine.Random.Range(raid.Options.AutoTurret.Min, raid.Options.AutoTurret.Max));

                if (RaidableBase.Has(victim.userID) && (raid.Options.NPC.IgnorePlayerTrapsTurrets || RaidableBase.Has(weapon) && !raid.BuiltList.ContainsKey(weapon)))
                {
                    return false;
                }

                if (weapon.OwnerID.IsSteamId())
                {
                    if (InRange2D(weapon.transform.position, raid.Location, raid.ProtectionRadius))
                    {
                        return victim.IsHuman() ? raid.AllowPVP : true;
                    }

                    return raid.AllowPVP || !victim.IsHuman();
                }
            }

            return true;
        }

        private object HandleAttacker(BasePlayer attacker, BasePlayer victim, HitInfo hitInfo, RaidableBase raid)
        {
            if (RaidableBase.Has(attacker.userID) && RaidableBase.Has(victim.userID))
            {
                return false;
            }

            if (attacker.userID == victim.userID)
            {
                return true;
            }

            if (PvpDelay.ContainsKey(victim.userID))
            {
                if (EventTerritory(attacker.transform.position))
                {
                    return true;
                }

                if (config.Settings.Management.PVPDelayAnywhere && PvpDelay.ContainsKey(attacker.userID))
                {
                    return true;
                }
            }

            if (config.Settings.Management.PVPDelayDamageInside && PvpDelay.ContainsKey(attacker.userID) && InRange2D(raid.Location, victim.transform.position, raid.ProtectionRadius))
            {
                return true;
            }

            if (!victim.IsHuman() && attacker.IsHuman())
            {
                return HandleNpcVictim(raid, victim, attacker);
            }
            else if (victim.IsHuman() && attacker.IsHuman())
            {
                return HandlePVPDamage(raid, victim, attacker, hitInfo);
            }
            else if (RaidableBase.Has(attacker.userID))
            {
                return HandleNpcAttacker(raid, victim, attacker, hitInfo);
            }

            return null;
        }

        private object HandleNpcVictim(RaidableBase raid, BasePlayer victim, BasePlayer attacker)
        {
            HumanoidBrain brain;
            if (!HumanoidBrains.TryGetValue(victim.userID, out brain))
            {
                return true;
            }

            if (config.Settings.Management.BlockMounts && attacker.GetMounted() || raid.ownerId.IsSteamId() && raid.CanEject() && !raid.IsAlly(attacker))
            {
                return false;
            }

            if (CanBlockOutsideDamage(raid, attacker, raid.Options.NPC.BlockOutsideDamageToNpcsInside))
            {
                return false;
            }

            var e = attacker.HasParent() ? attacker.GetParentEntity() : null;

            if (!e.IsNull() && (e is ScrapTransportHelicopter || e is HotAirBalloon || e is CH47Helicopter))
            {
                return false;
            }

            if (!raid.Options.NPC.CanLeave && raid.Options.NPC.BlockOutsideDamageOnLeave && !InRange(attacker.transform.position, raid.Location, raid.ProtectionRadius))
            {
                brain.Forget();

                return false;
            }

            brain.SetTarget(attacker);

            return true;
        }

        private object HandlePVPDamage(RaidableBase raid, BasePlayer victim, BasePlayer attacker, HitInfo hitInfo)
        {
            if (CanBlockOutsideDamage(raid, attacker, raid.Options.BlockOutsideDamageToPlayersInside) && !(hitInfo.WeaponPrefab is MLRSRocket))
            {
                return false;
            }

            if (IsPVE() && (!InRange(attacker.transform.position, raid.Location, raid.ProtectionRadius) || !InRange(victim.transform.position, raid.Location, raid.ProtectionRadius)))
            {
                return false;
            }

            if (raid.IsAlly(attacker.userID, victim.userID))
            {
                return raid.Options.AllowFriendlyFire;
            }

            return raid.AllowPVP;
        }

        private object HandleNpcAttacker(RaidableBase raid, BasePlayer victim, BasePlayer attacker, HitInfo hitInfo)
        {
            HumanoidBrain brain;
            if (!Instance.HumanoidBrains.TryGetValue(attacker.userID, out brain))
            {
                return true;
            }

            if (RaidableBase.Has(victim.userID) || (InRange2D(attacker.transform.position, raid.Location, raid.ProtectionRadius) && CanBlockOutsideDamage(raid, victim, raid.Options.BlockNpcDamageToPlayersOutside)))
            {
                return false;
            }

            if (brain.SenseRange <= brain.softLimitSenseRange && hitInfo.IsProjectile() && UnityEngine.Random.Range(0f, 100f) > raid.Options.NPC.Accuracy.Get(brain))
            {
                return false;
            }

            if (hitInfo.damageTypes.GetMajorityDamageType() == DamageType.Explosion)
            {
                hitInfo.UseProtection = false;
            }

            if (brain.attackType == HumanoidBrain.AttackType.BaseProjectile)
            {
                hitInfo.damageTypes.ScaleAll(raid.Options.NPC.Multipliers.ProjectileDamageMultiplier);
            }
            else if (brain.attackType == HumanoidBrain.AttackType.Melee)
            {
                hitInfo.damageTypes.ScaleAll(raid.Options.NPC.Multipliers.MeleeDamageMultiplier);
            }

            return true;
        }

        private object HandleEntityDamage(BaseCombatEntity entity, HitInfo hitInfo)
        {
            if (hitInfo.Initiator is SamSite)
            {
                return RaidableBase.Has(hitInfo.Initiator) ? true : (object)null;
            }

            var raid = RaidableBase.Get(entity.transform.position);

            if (raid == null || raid.IsDespawning)
            {
                return null;
            }

            if (!raid.Options.MLRS && hitInfo.WeaponPrefab is MLRSRocket)
            {
                return false;
            }

            if (entity.IsNpc || entity is PlayerCorpse)
            {
                return true;
            }

            if (raid.IsLoading || entity is DroppedItemContainer || hitInfo.damageTypes.GetMajorityDamageType() == DamageType.Decay)
            {
                return false;
            }

            if (raid.Options.Setup.FoundationsImmune && raid.Options.Setup.ForcedHeight != -1f)
            {
                if (raid.foundations.Count > 0 && entity.ShortPrefabName.StartsWith("foundation"))
                {
                    return false;
                }

                if (raid.floors == null && entity.ShortPrefabName.StartsWith("floor") && entity.transform.position.y - raid.Location.y <= 3f)
                {
                    return false;
                }
            }

            if (entity is BuildingBlock)
            {
                var block = entity as BuildingBlock;

                if (entity.OwnerID == 0)
                {
                    if (raid.Options.TwigImmune && block.grade == BuildingGrade.Enum.Twigs)
                    {
                        return false;
                    }
                    if (raid.Options.BlocksImmune)
                    {
                        return block.grade == BuildingGrade.Enum.Twigs;
                    }
                }
                else if (block.grade == BuildingGrade.Enum.Twigs)
                {
                    return true;
                }
            }

            if (raid.Options.TwigImmune && entity is BuildingBlock && (entity as BuildingBlock).grade == BuildingGrade.Enum.Twigs)
            {
                return false;
            }

            if (entity is BaseMountable || entity.PrefabName.Contains("modularcar"))
            {
                if (config.Settings.Management.MiniCollision && entity is MiniCopter && entity == hitInfo.Initiator)
                {
                    return false;
                }

                if (!config.Settings.Management.MountDamageFromPlayers && !ExcludedMounts.Contains(entity.prefabID) && hitInfo.Initiator is BasePlayer)
                {
                    raid.TryMessage(hitInfo.Initiator as BasePlayer, "NoMountedDamageTo");
                    return false;
                }
            }

            if (!RaidableBase.Has(entity))
            {
                return hitInfo.Initiator.IsNull() || RaidableBase.Has(hitInfo.Initiator) ? true : (object)null;
            }

            if (config.Settings.Management.BlockHelicopterDamage && IsHelicopter(hitInfo))
            {
                return false;
            }

            if (hitInfo.Initiator == entity && entity is AutoTurret)
            {
                return false;
            }

            var attacker = raid.GetInitiatorPlayer(hitInfo, entity);

            if (!attacker.IsReallyValid())
            {
                return hitInfo.Initiator.IsNull() || RaidableBase.Has(hitInfo.Initiator) ? true : (object)null;
            }

            if (!attacker.IsHuman())
            {
                if (entity.OwnerID == 0uL && !raid.Options.RaidingNpcs && !RaidableBase.Has(attacker.userID))
                {
                    return false;
                }

                if (hitInfo.damageTypes.Has(DamageType.Explosion))
                {
                    if (entity.OwnerID == 0uL && !(entity is BasePlayer) && RaidableBase.Has(attacker.userID))
                    {
                        return false;
                    }

                    return raid.BuiltList.ContainsKey(entity);
                }

                return true;
            }

            entity.lastAttacker = attacker;
            attacker.lastDealtDamageTime = Time.time;

            if (config.Settings.Management.BlockMounts && (attacker.GetMounted() || attacker.GetParentEntity() is BaseMountable))
            {
                raid.TryMessage(attacker, "NoMountedDamageFrom");
                return false;
            }

            if (CanBlockOutsideDamage(raid, attacker, raid.Options.BlockOutsideDamageToBaseInside) && !(hitInfo.WeaponPrefab is MLRSRocket))
            {
                raid.TryMessage(attacker, "NoDamageFromOutsideToBaseInside");
                return false;
            }

            if (raid.ownerId.IsSteamId() && raid.CanEject() && !raid.IsAlly(attacker))
            {
                raid.TryMessage(attacker, "NoDamageToEnemyBase");
                return false;
            }

            if (raid.Options.AutoTurret.AutoAdjust && raid.turrets.Count > 0 && entity is AutoTurret)
            {
                var turret = entity as AutoTurret;

                if (raid.turrets.Contains(turret) && turret.sightRange <= raid.Options.AutoTurret.SightRange)
                {
                    turret.sightRange = raid.Options.AutoTurret.SightRange * 2f;
                }
            }

            if (!raid.Options.ExplosionModifier.Equals(100) && hitInfo.damageTypes.Has(DamageType.Explosion))
            {
                float m = Mathf.Clamp(raid.Options.ExplosionModifier, 0f, 999f);

                hitInfo.damageTypes.Scale(DamageType.Explosion, m.Equals(0f) ? 0f : m / 100f);
            }

            if (raid.BuiltList.ContainsKey(entity))
            {
                return true;
            }

            raid.IsEngaged = true;
            raid.CheckDespawn();

            if (raid.IsOpened && IsLootingWeapon(hitInfo) && raid.AddLooter(attacker, hitInfo))
            {
                raid.TrySetOwner(attacker, entity, hitInfo);
            }

            if (!raid.CanHurtBox(entity))
            {
                raid.TryMessage(attacker, "NoDamageToBoxes");
                return false;
            }

            if (raid.Options.MLRS && hitInfo.WeaponPrefab is MLRSRocket)
            {
                raid.GetRaider(attacker).lastActiveTime = Time.time;
            }

            return true;
        }

        #endregion Hooks

        #region Spawn

        private static void Shuffle<T>(IList<T> list) // Fisher-Yates shuffle
        {
            int count = list.Count;
            int n = count;
            while (n-- > 0)
            {
                int k = UnityEngine.Random.Range(0, count);
                int j = UnityEngine.Random.Range(0, count);
                T value = list[k];
                list[k] = list[j];
                list[j] = value;
            }
        }

        private static Vector3 GetBuildingPrivilege(Vector3 target, float radius)
        {
            foreach (var tc in FindEntitiesOfType<BuildingPrivlidge>(target, radius))
            {
                if (!tc.IsKilled() && !RaidableBase.Has(tc))
                {
                    return tc.transform.position;
                }
            }
            return Vector3.zero;
        }

        public RaidableBase OpenEvent(RandomBase rb)
        {
            var raid = new GameObject().AddComponent<RaidableBase>();

            raid.stability = rb.stability;
            raid.MyInstance = this;
            raid.name = Name;
            raid.Definitions = _deployables;
            raid.SetAllowPVP(rb);
            raid.Location = rb.Position;
            raid.Options = rb.Profile.Options;
            raid.BaseName = rb.BaseName;
            raid.ProfileName = rb.Profile.ProfileName;
            raid.IsLoading = true;
            raid._undoLimit = Mathf.Clamp(raid.Options.Setup.DespawnLimit, 1, 500);

            if (config.Weapons.SamSiteRange > 0f)
            {
                Subscribe(nameof(OnSamSiteTarget));
            }

            if (!raid.Options.MLRS)
            {
                Subscribe(nameof(OnMlrsFire));
            }

            if (config.Settings.NoWizardry && Wizardry.CanCall())
            {
                Subscribe(nameof(OnActiveItemChanged));
            }

            if (config.Settings.BlacklistedCommands.Count > 0)
            {
                Subscribe(nameof(OnPlayerCommand));
                Subscribe(nameof(OnServerCommand));
            }

            if (!IsPVE())
            {
                Subscribe(nameof(OnEntityTakeDamage));
            }

            Subscribe(nameof(CanEntityTakeDamage));
            Subscribe(nameof(OnEntityEnter));
            Subscribe(nameof(CanBuild));

            data.TotalEvents++;
            raid.SetupCollider();

            Raids.Add(raid);

            return raid;
        }

        #endregion

        #region Paste

        protected bool IsGridLoading => GridController.gridCoroutine != null;

        protected bool IsPasteAvailable => !Raids.Exists(raid => raid.IsLoading);

        private bool PasteBuilding(RandomBase rb, bool bypass = false)
        {
            if (bypass || !RaidableBase.IsSpawnerBusy)
            {
                Queues.Messages.Print($"{rb.BaseName} trying to paste at {rb.Position}");

                loadCoroutines.Add(ServerMgr.Instance.StartCoroutine(LoadCopyPasteFile(rb)));

                return true;
            }

            return false;
        }

        private void StopLoadCoroutines()
        {
            if (setupCopyPasteObstructionRadius != null)
            {
                ServerMgr.Instance.StopCoroutine(setupCopyPasteObstructionRadius);
                setupCopyPasteObstructionRadius = null;
            }
            foreach (var co in loadCoroutines.ToList())
            {
                if (co != null)
                {
                    ServerMgr.Instance.StopCoroutine(co);
                }
            }
            Queues?.StopCoroutine();
            Automated?.StopCoroutine(RaidableType.Scheduled);
            Automated?.StopCoroutine(RaidableType.Maintained);
            GridController.StopCoroutine();
            temporaryData?.StopCoroutine();
        }

        private bool IsPrefabFoundation(Dictionary<string, object> entity)
        {
            var prefabname = entity["prefabname"].ToString();

            return prefabname.Contains("/foundation.") || prefabname.EndsWith("diesel_collectable.prefab") && entity.ContainsKey("skinid") && entity["skinid"] == "1337424001";
        }

        private bool IsPrefabFloor(Dictionary<string, object> entity)
        {
            return entity["prefabname"].ToString().Contains("/floor");
        }

        private IEnumerator SetupCopyPasteObstructionRadius()
        {
            foreach (var profile in Buildings.Profiles)
            {
                var radius = profile.Value.Options.ProtectionRadii.Obstruction == -1 ? 0f : GetObstructionRadius(profile.Value.Options.ProtectionRadii, RaidableType.None);
                foreach (var extra in profile.Value.Options.AdditionalBases)
                {
                    yield return SetupCopyPasteObstructionRadius(extra.Key, radius);
                }
                yield return SetupCopyPasteObstructionRadius(profile.Key, radius);
            }
            setupCopyPasteObstructionRadius = null;
        }

        private IEnumerator SetupCopyPasteObstructionRadius(string baseName, float radius)
        {
            var filename = $"copypaste/{baseName}";

            if (!Interface.Oxide.DataFileSystem.ExistsDatafile(filename))
            {
                yield break;
            }

            DynamicConfigFile data;

            try
            {
                data = Interface.Oxide.DataFileSystem.GetDatafile(filename);
            }
            catch (Exception ex)
            {
                Queues.Messages.Log(baseName, $"{baseName} could not be read from the disk #1: {ex}");
                yield break;
            }

            if (data["entities"] == null)
            {
                Queues.Messages.Log(baseName, $"{baseName} is missing entity data");
                yield break;
            }

            var entities = data["entities"] as List<object>;
            var foundations = new List<Vector3>();
            var floors = new List<Vector3>();
            int checks = 0;
            float x = 0f;
            float z = 0f;

            foreach (Dictionary<string, object> entity in entities)
            {
                if (++checks >= 1000)
                {
                    checks = 0;
                    yield return CoroutineEx.waitForSeconds(0.0025f);
                }
                if (!entity.ContainsKey("prefabname") || !entity.ContainsKey("pos"))
                {
                    continue;
                }
                var axes = entity["pos"] as Dictionary<string, object>;
                var position = new Vector3(Convert.ToSingle(axes?["x"]), Convert.ToSingle(axes?["y"]), Convert.ToSingle(axes?["z"]));
                if (IsPrefabFoundation(entity))
                {
                    foundations.Add(position);
                    x += position.x;
                    z += position.z;
                }
                if (IsPrefabFloor(entity))
                {
                    floors.Add(position);
                }
            }

            if (foundations.Count == 0)
            {
                foreach (var position in floors)
                {
                    foundations.Add(position);
                    x += position.x;
                    z += position.z;
                }
            }

            var center = new Vector3(x / foundations.Count, 0f, z / foundations.Count);

            center.y = GetSpawnHeight(center);

            if (radius == 0f)
            {
                foundations.Sort((a, b) => (a - center).sqrMagnitude.CompareTo((b - center).sqrMagnitude));

                radius = Vector3.Distance(foundations[0], foundations[foundations.Count - 1]) + 3f;
            }

            var pasteData = PasteData.Get(baseName);

            pasteData.radius = Mathf.Ceil(Mathf.Max(CELL_SIZE, radius));
            pasteData.foundations = foundations;
            pasteData.valid = true;
        }

        private Plugin CopyPaste => plugins.Find("CopyPaste");

        private IEnumerator LoadCopyPasteFile(RandomBase rb)
        {
            Core.Configuration.DynamicConfigFile data;

            try
            {
                data = Interface.Oxide.DataFileSystem.GetDatafile($"copypaste/{rb.BaseName}");
            }
            catch (Exception ex)
            {
                Queues.Messages.Log(rb.BaseName, $"{rb.BaseName} could not be read from the disk #2: {ex}");
                yield break;
            }

            var pasteData = PasteData.Get(rb.BaseName);

            yield return ApplyStartPositionAdjustment(rb, data, pasteData);

            if (pasteData.foundations == null)
            {
                Queues.Messages.Log(rb.BaseName, $"{rb.BaseName} is missing foundation/floor data");
                yield break;
            }

            yield return ParseListedOptions(rb);

            var entities = data["entities"] as List<object>;

            if (entities == null)
            {
                Queues.Messages.Log(rb.BaseName, $"{rb.BaseName} is missing entity data");
                yield break;
            }

            var preloadData = CopyPaste.Call("PreLoadData", entities, rb.Position, 0f, true, true, false, true) as HashSet<Dictionary<string, object>>;

            yield return TryApplyAutoHeight(rb, preloadData);

            if (IsInstanceValid)
            {
                var raid = OpenEvent(rb);
                var protocol = data["protocol"] == null ? new Dictionary<string, object>() : data["protocol"] as Dictionary<string, object>;
                var result = CopyPaste.Call("Paste", new object[] { preloadData, protocol, false, rb.Position, _consolePlayer, rb.stability, 0f, rb.heightAdj, false, CreatePastedCallback(raid, rb), CreateSpawnCallback(raid), rb.BaseName, false });
                if (result == null)
                {
                    Queues.Messages.Print($"CopyPaste {CopyPaste.Version} did not respond for {rb.BaseName}!");
                    raid.Despawn();
                }
                else Queues.Messages.Print($"{rb.BaseName} is pasting at {rb.Position}");
            }
            else Queues.Messages.Print($"{rb.BaseName} cannot paste; instance is invalid #2");
        }

        private Action CreatePastedCallback(RaidableBase raid, RandomBase rb)
        {
            return new Action(() =>
            {
                SaveTemporaryData();

                if (raid.IsUnloading)
                {
                    raid.Despawn();
                }
                else
                {
                    raid.Init(rb);
                }
            });
        }

        private Action<BaseEntity> CreateSpawnCallback(RaidableBase raid)
        {
            return new Action<BaseEntity>(e =>
            {
                if (!e.IsKilled())
                {
                    if (raid.IsUnloading || unityEngineScripts.Contains(e.ShortPrefabName))
                    {
                        NextTick(e.SafelyKill);
                        return;
                    }
                    if (e.ShortPrefabName == "foundation.triangle" || e.ShortPrefabName == "foundation" || e.skinID == 1337424001 && e is CollectibleEntity)
                    {
                        raid.foundations.Add(e.transform.position);
                    }
                    else if (e.ShortPrefabName.Contains("floor"))
                    {
                        raid.floors.Add(e.transform.position);
                    }
                    if (!raid.stability && e is BuildingBlock)
                    {
                        (e as BuildingBlock).grounded = true;
                    }
                    else if (raid.Options.EmptyAll && e is StorageContainer)
                    {
                        raid.TryEmptyContainer(e as StorageContainer);
                    }
                    foreach (var slot in _checkSlots)
                    {
                        raid.AddEntity(e.GetSlot(slot));
                    }
                    e.OwnerID = 0;
                    raid.AddEntity(e);
                }
            });
        }

        private IEnumerator ApplyStartPositionAdjustment(RandomBase rb, DynamicConfigFile data, PasteData pasteData)
        {
            var foundations = new List<Vector3>();
            float x = 0f, z = 0f;

            if (!pasteData.valid)
            {
                yield return Instance.SetupCopyPasteObstructionRadius(rb.BaseName, rb.Profile.Options.ProtectionRadii.Obstruction == -1f ? 0f : GetObstructionRadius(rb.Profile.Options.ProtectionRadii, RaidableType.None));
            }

            if (pasteData.foundations == null)
            {
                Queues.Messages.Log(rb.BaseName, $"{rb.BaseName} is missing foundation/floor data");
                yield break;
            }

            foreach (var foundation in pasteData.foundations)
            {
                var a = foundation + rb.Position;
                a.y = GetSpawnHeight(a);
                foundations.Add(a);
                x += a.x;
                z += a.z;
            }

            var center = new Vector3(x / foundations.Count, 0f, z / foundations.Count);

            center.y = GetSpawnHeight(center);

            rb.Position = rb.Position + (rb.Position - center);

            if (rb.Profile.Options.Setup.ForcedHeight == -1)
            {
                rb.Position.y = GetSpawnHeight(rb.Position);

                TryApplyCustomAutoHeight(rb, pasteData);
                TryApplyMultiFoundationSupport(rb, pasteData);

                rb.Position.y += rb.Profile.Options.Setup.PasteHeightAdjustment;
            }
            else rb.Position.y = rb.Profile.Options.Setup.ForcedHeight;

            yield return CoroutineEx.waitForFixedUpdate;
        }

        private IEnumerator TryApplyAutoHeight(RandomBase rb, HashSet<Dictionary<string, object>> preloadData)
        {
            if (rb.autoHeight && !config.Settings.Experimental.Contains(ExperimentalSettings.Type.AutoHeight, rb))
            {
                var bestHeight = Convert.ToSingle(CopyPaste.Call("FindBestHeight", preloadData, rb.Position));
                int checks = 0;

                rb.heightAdj = bestHeight - rb.Position.y;

                foreach (var entity in preloadData)
                {
                    if (++checks >= 1000)
                    {
                        checks = 0;
                        yield return CoroutineEx.waitForSeconds(0.0025f);
                    }

                    var pos = (Vector3)entity["position"];

                    pos.y += rb.heightAdj;

                    entity["position"] = pos;
                }
            }
        }

        private void TryApplyCustomAutoHeight(RandomBase rb, PasteData pasteData)
        {
            if (config.Settings.Experimental.Contains(ExperimentalSettings.Type.AutoHeight, rb))
            {
                foreach (var foundation in pasteData.foundations)
                {
                    var a = foundation + rb.Position;

                    if (a.y < rb.Position.y)
                    {
                        rb.Position.y += rb.Position.y - a.y;
                        return;
                    }
                    else
                    {
                        rb.Position.y -= a.y - rb.Position.y;
                        return;
                    }
                }
            }
        }

        private void TryApplyMultiFoundationSupport(RandomBase rb, PasteData pasteData)
        {
            float j = 0f, k = 0f, y = 0f;
            for (int i = 0; i < pasteData.foundations.Count; i++)
            {
                y = (float)Math.Round(pasteData.foundations[i].y, 1);
                j = Mathf.Max(y, j);
                k = Mathf.Min(y, k);
            }
            if (j != 0f && config.Settings.Experimental.Contains(ExperimentalSettings.Type.MultiFoundation, rb))
            {
                rb.Position.y += j + 1f;
            }
            else if (k != 0f && config.Settings.Experimental.Contains(ExperimentalSettings.Type.Bunker, rb))
            {
                y = rb.Position.y + Mathf.Abs(k);
                if (y < rb.Position.y)
                {
                    rb.Position.y = y + 1.5f;
                }
            }
        }

        [HookMethod("GetSpawnHeight")]
        public float GetSpawnHeight(Vector3 a, bool flag = true, bool shouldSkipSmallRock = false) => SpawnsController.GetSpawnHeight(a, flag, shouldSkipSmallRock);

        private IEnumerator ParseListedOptions(RandomBase rb)
        {
            rb.autoHeight = false;

            float height = 0f;
            List<PasteOption> pasteOptions = rb.Profile.Options.PasteOptions;

            foreach (var kvp in rb.Profile.Options.AdditionalBases)
            {
                if (kvp.Key.Equals(rb.BaseName, StringComparison.OrdinalIgnoreCase))
                {
                    pasteOptions = kvp.Value;
                    break;
                }
            }

            for (int i = 0; i < pasteOptions.Count; i++)
            {
                string key = pasteOptions[i].Key.ToLower();
                string value = pasteOptions[i].Value.ToLower();

                if (key == "stability")
                {
                    rb.stability = value == "true";
                }
                if (key == "autoheight")
                {
                    rb.autoHeight = value == "true";
                }
                if (key == "height" && float.TryParse(value, out height))
                {
                    rb.Position.y += height;
                }
            }

            yield return CoroutineEx.waitForFixedUpdate;
        }

        private bool SpawnRandomBase(RaidableType type, string baseName = null, bool isAdmin = false, BasePlayer owner = null, IPlayer user = null)
        {
            lastSpawnRequestTime = Time.realtimeSinceStartup;

            var profile = GetBuilding(type, baseName);
            bool checkTerrain, validProfile = IsProfileValid(profile);
            var spawns = GetSpawns(type, profile.Value, out checkTerrain);

            if (validProfile && spawns != null)
            {
                return AddSpawnToQueue(profile, checkTerrain, type, spawns, owner, user, Vector3.zero);
            }
            else if (type == RaidableType.Maintained || type == RaidableType.Scheduled)
            {
                Queues.Messages.PrintAll();
            }
            else Queues.Messages.Add(GetDebugMessage(validProfile, isAdmin, owner?.UserIDString, baseName, profile.Value?.Options));

            return false;
        }

        private bool AddSpawnToQueue(KeyValuePair<string, BaseProfile> profile, bool checkTerrain, RaidableType type, RaidableSpawns spawns, BasePlayer owner = null, IPlayer user = null, Vector3 a = default(Vector3))
        {
            var rb = new RandomBase();

            rb.Position = a;
            rb.checkTerrain = checkTerrain;
            rb.spawns = spawns;
            rb.type = type;
            rb.Profile = profile.Value;
            rb.BaseName = profile.Key;
            rb.owner = owner;
            rb.user = user;
            rb.userid = owner?.userID ?? 0;
            rb.typeDistance = GetDistance(rb.type);
            rb.protectionRadius = rb.options.ProtectionRadius(rb.type);
            rb.safeRadius = Mathf.Max(rb.options.ArenaWalls.Radius, rb.protectionRadius);
            rb.buildRadius = Mathf.Max(config.Settings.Management.CupboardDetectionRadius, rb.options.ArenaWalls.Radius, rb.protectionRadius) + 5f;
            rb.pasteData = PasteData.Get(profile.Key);

            Queues.Add(rb);

            return true;
        }

        private string GetDebugMessage(bool validProfile, bool isAdmin, string id, string baseName, BuildingOptions options)
        {
            if (options != null && !options.Enabled)
            {
                return mx("Profile Not Enabled", id, baseName);
            }

            if (!validProfile)
            {
                return Instance.Queues.Messages.GetLast(id);
            }

            if (!string.IsNullOrEmpty(baseName))
            {
                if (!FileExists(baseName))
                {
                    return mx("FileDoesNotExist", id);
                }
                else if (!Buildings.IsConfigured(baseName))
                {
                    return mx("BuildingNotConfigured", id);
                }
            }

            return Buildings.Profiles.Count == 0 ? mx("NoBuildingsConfigured", id) : Instance.Queues.Messages.GetLast(id);
        }

        private RaidableSpawns GetSpawns(RaidableType type, BaseProfile profile, out bool checkTerrain)
        {
            RaidableSpawns spawns;
            checkTerrain = false;

            switch (type)
            {
                case RaidableType.Maintained: if (GridController.Spawns.TryGetValue(RaidableType.Maintained, out spawns)) return spawns; break;
                case RaidableType.Manual: if (GridController.Spawns.TryGetValue(RaidableType.Manual, out spawns)) return spawns; break;
                case RaidableType.Scheduled: if (GridController.Spawns.TryGetValue(RaidableType.Scheduled, out spawns)) return spawns; break;
            }

            checkTerrain = true;
            return GridController.Spawns.TryGetValue(RaidableType.Grid, out spawns) ? spawns : null;
        }

        private KeyValuePair<string, BaseProfile> GetBuilding(RaidableType type, string baseName)
        {
            var list = new List<KeyValuePair<string, BaseProfile>>();
            bool isBaseNull = string.IsNullOrEmpty(baseName);

            foreach (var profile in Buildings.Profiles)
            {
                if (MustExclude(type, profile.Value.Options.AllowPVP))
                {
                    Queues.Messages.Add($"{type} is not configured to include {(profile.Value.Options.AllowPVP ? "PVP" : "PVE")} bases.");
                }

                if (FileExists(profile.Key) && Cycle.CanSpawn(type, profile.Key))
                {
                    if (isBaseNull)
                    {
                        list.Add(profile);
                    }
                    else if (profile.Key.Equals(baseName, StringComparison.OrdinalIgnoreCase))
                    {
                        return profile;
                    }
                }

                foreach (var extra in profile.Value.Options.AdditionalBases)
                {
                    if (!FileExists(extra.Key) || !Cycle.CanSpawn(type, extra.Key))
                    {
                        continue;
                    }

                    var clone = BaseProfile.Clone(profile.Value);
                    var kvp = new KeyValuePair<string, BaseProfile>(extra.Key, clone);

                    kvp.Value.Options.PasteOptions = extra.Value.ToList();

                    if (isBaseNull)
                    {
                        list.Add(kvp);
                    }
                    else if (extra.Key.Equals(baseName, StringComparison.OrdinalIgnoreCase))
                    {
                        return kvp;
                    }
                }
            }

            if (list.Count == 0)
            {
                if (!AnyFileExists)
                {
                    Queues.Messages.Print("No copypaste file in any profile exists?");
                }
                else Queues.Messages.Print($"Building is unavailable", type);

                return default(KeyValuePair<string, BaseProfile>);
            }

            return list.GetRandom();
        }

        private static bool IsProfileValid(KeyValuePair<string, BaseProfile> profile)
        {
            if (string.IsNullOrEmpty(profile.Key) || profile.Value == null || profile.Value.Options == null)
            {
                return false;
            }

            return profile.Value.Options.Enabled;
        }

        private bool AnyFileExists;

        private static bool FileExists(string file)
        {
            if (!file.Contains(Path.DirectorySeparatorChar.ToString()))
            {
                bool exists = Interface.Oxide.DataFileSystem.ExistsDatafile($"copypaste{Path.DirectorySeparatorChar}{file}");

                if (exists)
                {
                    Instance.AnyFileExists = true;
                }

                return exists;
            }

            return Interface.Oxide.DataFileSystem.ExistsDatafile(file);
        }

        #endregion

        #region Commands

        private void CommandReloadConfig(IPlayer user, string command, string[] args)
        {
            if (user.IsServer || user.ToPlayer().IsAdmin)
            {
                if (!IsPasteAvailable)
                {
                    user.Reply(mx("PasteOnCooldown", user.Id));
                    return;
                }

                SetOnSun(false);

                user.Reply(mx("ReloadConfig", user.Id));
                LoadConfig();
                Automated.IsMaintainedEnabled = config.Settings.Maintained.Enabled;
                Automated.StartCoroutine(RaidableType.Maintained, user);
                Automated.IsScheduledEnabled = config.Settings.Schedule.Enabled;
                Automated.StartCoroutine(RaidableType.Scheduled, user);
                user.Reply(mx("ReloadInit", user.Id));
                Initialize();
            }
        }

        private void Initialize()
        {
            Instance = this;
            //if (!isConfigurationInitialized)
            //{
            //    return;
            //}
            GridController.LoadSpawns();
            InitializeSkins();
            SpawnsController.SetupZones(ZoneManager);
            Reinitialize();
            CreateDefaultFiles();
            SetOnSun(true);
            GridController.Setup();
        }

        private void CommandBlockRaids(BasePlayer player, string command, string[] args)
        {
            if (args.Length != 1) { Player.Message(player, "You must specify a radius"); return; }
            float radius;
            if (!float.TryParse(args[1], out radius) || radius <= 5f) { Player.Message(player, $"Invalid radius {args[1]} specified"); return; }
            if (config.Settings.Management.BlockedPositions.RemoveAll(x => InRange(player.transform.position, x.position, radius)) == 0)
            {
                config.Settings.Management.BlockedPositions.Add(new ManagementSettingsLocations(player.transform.position, radius));
                Player.Message(player, $"Block added; raids will no longer spawn within {radius}m of this position");
                SaveConfig();
            }
            else Player.Message(player, "Block removed; raids are now allowed to spawn at this position");
        }

        private void CommandRaidHunter(IPlayer user, string command, string[] args)
        {
            var player = user.ToPlayer();
            bool isAdmin = user.IsServer || player.IsAdmin;
            string arg = args.Length >= 1 ? args[0].ToLower() : string.Empty;

            switch (arg)
            {
                case "blockraids":
                    {
                        if (isAdmin)
                        {
                            CommandBlockRaids(player, command, args);
                        }
                        return;
                    }
                case "version":
                    {
                        user.Reply($"Version: {Version}");
                        return;
                    }
                case "invite":
                    {
                        CommandInvite(player, args);
                        return;
                    }
                case "resettime":
                    {
                        if (isAdmin)
                        {
                            data.RaidTime = DateTime.MinValue.ToString();
                        }

                        return;
                    }
                case "wipe":
                    {
                        if (isAdmin)
                        {
                            wiped = true;
                            CheckForWipe();
                        }

                        return;
                    }
                case "ignore_restart":
                    {
                        if (isAdmin)
                        {
                            bypassRestarting = !bypassRestarting;
                            user.Reply($"Bypassing restart check: {bypassRestarting}");
                        }

                        return;
                    }
                case "savefix":
                    {
                        if (user.IsAdmin || user.HasPermission("raidablebases.allow"))
                        {
                            int removed = BaseEntity.saveList.RemoveWhere(e => e.IsKilled());

                            user.Reply($"Removed {removed} invalid entities from the save list.");

                            if (SaveRestore.IsSaving)
                            {
                                SaveRestore.IsSaving = false;
                                user.Reply("Server save has been canceled. You must type server.save again, and then restart your server.");
                            }
                            else user.Reply("Server save is operating normally.");
                        }

                        return;
                    }
                case "tp":
                    {
                        if (player.IsReallyValid() && (isAdmin || user.HasPermission("raidablebases.allow")))
                        {
                            RaidableBase raid = null;
                            float num = 9999f;

                            foreach (var other in Raids)
                            {
                                float num2 = player.Distance(other.Location);

                                if (num2 > other.ProtectionRadius * 2f && num2 < num)
                                {
                                    num = num2;
                                    raid = other;
                                }
                            }

                            if (raid != null)
                            {
                                player.Teleport(raid.Location);
                            }
                        }

                        return;
                    }
                case "isblocked":
                    {
                        if (isAdmin)
                        {
                            user.Reply(SpawnsController.IsLocationBlocked(new Vector3(user.Position().X, user.Position().Y, user.Position().Z)).ToString());
                        }
                        return;
                    }
                case "grid":
                    {
                        if (player.IsReallyValid() && (isAdmin || user.HasPermission("raidablebases.ddraw")))
                        {
                            ShowGrid(player, args.Length == 2 && args[1] == "all");
                        }

                        return;
                    }
                case "ladder":
                case "lifetime":
                    {
                        ShowLadder(user, args);
                        return;
                    }
                case "queue":
                    {
                        user.Reply($"There are {Queues.queue.Count} events waiting in the queue.");
                        if (Queues.queue.Count > 0)
                        {
                            foreach (var spq in Queues.queue)
                            {
                                user.Reply($"{spq.type} ({spq.attempts} attempts");
                            }
                        }
                        return;
                    }
                case "queue_clear":
                    {
                        if (isAdmin)
                        {
                            int num = Queues.queue.Count;
                            Queues.queue.Clear();
                            user.Reply($"Cleared and refunded {num} in the queue.");
                        }
                        return;
                    }

            }

            if (config.RankedLadder.Enabled)
            {
                PlayerInfo playerInfo = PlayerInfo.Get(user.Id);

                user.Reply(m("Wins", user.Id, PlayerInfo.Get(user.Id).Raids, config.Settings.HunterCommand));
            }

            if (Raids.Count == 0 && Automated.IsScheduledEnabled)
            {
                ShowNextScheduledEvent(user);
                return;
            }

            if (player.IsReallyValid())
            {
                DrawRaidLocations(player, isAdmin || player.HasPermission("raidablebases.ddraw"));
            }
        }

        private void CommandInvite(BasePlayer player, string[] args)
        {
            if (player == null) return;
            if (args.Length < 1) { Message(player, "Invite Usage", config.Settings.HunterCommand); return; }
            var target = RustCore.FindPlayer(args[0]);
            if (target == null) { Message(player, "TargetNotFoundId", args[0]); return; }
            var raid = Raids.FirstOrDefault(x => x.ownerId == player.userID);
            if (raid == null) { Message(player, "Invite Ownership Error"); return; }
            Raider raider;
            if (!raid.raiders.TryGetValue(target.userID, out raider)) raid.raiders[target.userID] = raider = new Raider(target);
            raider.IsAlly = true;
            Message(player, "Invite Success", target.displayName);
            Message(target, "Invite Allowed", player.displayName);
        }

        protected void DrawRaidLocations(BasePlayer player, bool hasPerm)
        {
            if (!player.HasPermission("raidablebases.block.filenames") && !player.IsAdmin && !player.IsDeveloper)
            {
                foreach (var raid in Raids)
                {
                    if (InRange2D(raid.Location, player.transform.position, 100f))
                    {
                        Player.Message(player, string.Format("{0} @ {1} ({2})", raid.BaseName, raid.Location, PositionToGrid(raid.Location)));
                    }
                }
            }

            if (hasPerm)
            {
                AdminCommand(player, () =>
                {
                    foreach (var raid in Raids)
                    {
                        int num = BasePlayer.activePlayerList.Sum(x => x.IsReallyValid() && x.Distance(raid.Location) <= raid.ProtectionRadius * 3f ? 1 : 0);
                        int distance = Mathf.CeilToInt(player.transform.position.Distance(raid.Location));
                        string message = mx("RaidMessage", player.UserIDString, distance, num);
                        string flag = mx(raid.AllowPVP ? "PVPFlag" : "PVEFlag", player.UserIDString);

                        DrawText(player, 15f, Color.yellow, raid.Location, string.Format("<size=24>{0}{1} {2} [{3} {4}] {5}</size>", raid.BaseName, flag, raid.Mode(player.UserIDString, true), message, PositionToGrid(raid.Location), raid.Location));

                        foreach (var ri in raid.raiders.Values.Where(x => x.IsAlly && x.player.IsReallyValid()))
                        {
                            DrawText(player, 15f, Color.yellow, ri.player.transform.position, $"<size=24>{mx("Ally", player.UserIDString).Replace(":", string.Empty)}</size>");
                        }

                        if (!raid.ownerId.IsSteamId())
                        {
                            continue;
                        }

                        var owner = raid.GetOwner();

                        if (!owner.IsKilled())
                        {
                            DrawText(player, 15f, Color.yellow, owner.transform.position, $"<size=24>{mx("Owner", player.UserIDString).Replace(":", string.Empty)}</size>");
                        }
                    }
                });
            }
        }

        protected void ShowNextScheduledEvent(IPlayer user)
        {
            string message;
            double time = GridController.GetRaidTime();

            if (BasePlayer.activePlayerList.Count < config.Settings.Schedule.PlayerLimit)
            {
                message = mx("Not Enough Online", user.Id, config.Settings.Schedule.PlayerLimit);
            }
            else if (BasePlayer.activePlayerList.Count > config.Settings.Schedule.PlayerLimitMax)
            {
                message = mx("Too Many Online", user.Id, config.Settings.Schedule.PlayerLimitMax);
            }
            else message = FormatTime(time, user.Id);

            user.Reply(m("Next", user.Id, message));
        }

        protected void ShowLadder(IPlayer user, string[] args)
        {
            if (!config.RankedLadder.Enabled || config.RankedLadder.Top < 1)
            {
                return;
            }

            if (args.Length == 2 && args[1].ToLower() == "resetme")
            {
                data.Players[user.Id] = new PlayerInfo();
                user.Reply("Your ranked stats have been reset.");
                return;
            }

            string key = args[0].ToLower();

            if (data.Players.Count == 0)
            {
                user.Reply(m("Ladder Insufficient Players", user.Id));
                return;
            }

            int rank = 0;
            bool isByWipe = key == "ladder";
            var ladder = GetLadder(key);

            ladder.Sort((x, y) => y.Value.CompareTo(x.Value));

            user.Reply(m(isByWipe ? "RankedLadder" : "RankedTotal", user.Id, config.RankedLadder.Top, mx("Normal")));

            foreach (var kvp in ladder.Take(config.RankedLadder.Top))
            {
                NotifyPlayer(user, ++rank, kvp);
            }

            ladder.Clear();
        }

        protected void ShowGrid(BasePlayer player, bool showAll)
        {
            AdminCommand(player, () =>
            {
                RaidableSpawns spawns;
                if (!GridController.Spawns.TryGetValue(RaidableType.Grid, out spawns))
                {
                    return;
                }

                foreach (var rsl in spawns.Spawns)
                {
                    if (showAll || InRange2D(rsl.Location, player.transform.position, 1000f))
                    {
                        DrawText(player, 30f, Color.green, rsl.Location, "X");
                    }
                }

                foreach (CacheType cacheType in Enum.GetValues(typeof(CacheType)))
                {
                    var color = cacheType == CacheType.Generic ? Color.red : cacheType == CacheType.Temporary ? Color.cyan : cacheType == CacheType.Privilege ? Color.yellow : cacheType == CacheType.Submerged ? Color.blue : Color.red;
                    var text = cacheType == CacheType.Generic ? "X" : cacheType == CacheType.Temporary ? "C" : cacheType == CacheType.Privilege ? "TC" : cacheType == CacheType.Submerged ? "W" : "X";

                    foreach (var rsl in spawns.Inactive(cacheType))
                    {
                        if (showAll || InRange2D(rsl.Location, player.transform.position, 1000f))
                        {
                            DrawText(player, 30f, color, rsl.Location, text);
                        }
                    }
                }

                foreach (var cmi in SpawnsController.Monuments)
                {
                    DrawSphere(player, 30f, Color.blue, cmi.position, cmi.radius);
                    DrawText(player, 30f, Color.cyan, cmi.position, $"<size=16>{cmi.text} ({cmi.radius})</size>");
                }
            });
        }

        protected List<KeyValuePair<string, int>> GetLadder(string arg)
        {
            var ladder = new List<KeyValuePair<string, int>>();
            bool isLadder = arg.ToLower() == "ladder";

            foreach (var entry in data.Players)
            {
                int value = isLadder ? entry.Value.Raids : entry.Value.TotalRaids;

                if (value > 0)
                {
                    ladder.Add(new KeyValuePair<string, int>(entry.Key, value));
                }
            }

            return ladder;
        }

        private void NotifyPlayer(IPlayer user, int rank, KeyValuePair<string, int> kvp)
        {
            PlayerInfo playerInfo = PlayerInfo.Get(kvp.Key);
            playerInfo.ResetExpiredDate();
            string name = covalence.Players.FindPlayerById(kvp.Key)?.Name ?? kvp.Key;
            string value = kvp.Value.ToString("N0");
            string message = mx("NotifyPlayerMessageFormat", user.Id);

            message = message.Replace("{rank}", rank.ToString());
            message = message.Replace("{name}", name);
            message = message.Replace("{value}", value);

            user.Reply(message);
        }

        private void CommandRaidBase(IPlayer user, string command, string[] args)
        {
            var player = user.ToPlayer();
            bool isAllowed = user.IsServer || player.IsAdmin || user.HasPermission("raidablebases.allow");
            if (!CanCommandContinue(player, user, isAllowed, args))
            {
                return;
            }
            if (command == config.Settings.EventCommand) // rbe
            {
                ProcessEventCommand(user, player, isAllowed, args);
            }
            else if (command == config.Settings.ConsoleCommand) // rbevent
            {
                ProcessConsoleCommand(user, player, isAllowed, args);
            }
        }

        protected void ProcessEventCommand(IPlayer user, BasePlayer player, bool isAllowed, string[] args) // rbe
        {
            if (!isAllowed || !player.IsReallyValid())
            {
                return;
            }

            var baseName = args.FirstOrDefault(value => FileExists(value));
            var profile = GetBuilding(RaidableType.Manual, baseName);

            if (!IsProfileValid(profile))
            {
                user.Reply(profile.Value == null ? m("BuildingNotConfigured", user.Id) : GetDebugMessage(false, true, user.Id, profile.Key, profile.Value.Options));
                return;
            }

            RaycastHit hit;
            if (!Physics.Raycast(player.eyes.HeadRay(), out hit, isAllowed ? Mathf.Infinity : 100f, targetMask2, QueryTriggerInteraction.Ignore))
            {
                user.Reply(m("LookElsewhere", user.Id));
                return;
            }

            CacheType cacheType;
            var safeRadius = Mathf.Max(M_RADIUS * 2f, profile.Value.Options.ArenaWalls.Radius);
            var safe = player.IsAdmin || SpawnsController.IsAreaSafe(hit.point, safeRadius, safeRadius, manualMask, out cacheType, RaidableType.Manual);

            if (!safe && !player.IsFlying && InRange(player.transform.position, hit.point, 50f))
            {
                user.Reply(m("PasteIsBlockedStandAway", user.Id));
                return;
            }

            bool pasted = false;

            if (safe && (isAllowed || !SpawnsController.IsMonumentPosition(hit.point, profile.Value.Options.ProtectionRadius(RaidableType.Manual))))
            {
                var spawns = GridController.Spawns.Values.FirstOrDefault(s => s.Spawns.Exists(t => InRange2D(t.Location, hit.point, M_RADIUS)));
                var rb = new RandomBase(profile.Key, profile.Value, hit.point, RaidableType.Manual, spawns);
                if (PasteBuilding(rb, isAllowed))
                {
                    DrawText(player, 10f, Color.red, hit.point, rb.BaseName);
                    if (ConVar.Server.hostname.Contains("Test Server"))
                    {
                        var data = PasteData.Get(rb.BaseName);
                        DrawSphere(player, 30f, Color.blue, hit.point, data.radius);
                    }
                    pasted = true;
                }
            }
            else user.Reply(m("PasteIsBlocked", user.Id));

            if (!pasted && Queues.Messages.Any())
            {
                user.Reply(IsGridLoading ? m("GridIsLoading") : Queues.Messages.GetLast(user.Id));
            }
        }

        protected void ProcessConsoleCommand(IPlayer user, BasePlayer player, bool isAllowed, string[] args) // rbevent
        {
            if (IsGridLoading && !user.IsAdmin)
            {
                int count = GridController.Spawns.ContainsKey(RaidableType.Grid) ? GridController.Spawns[RaidableType.Grid].Spawns.Count : 0;
                user.Reply(m("GridIsLoadingFormatted", user.Id, (Time.realtimeSinceStartup - GridController.gridTime).ToString("N02"), count));
                return;
            }

            QueueNotification(player, "BaseQueued", Queues.queue.Count);
            string baseName = args.FirstOrDefault(value => FileExists(value));
            SpawnRandomBase(RaidableType.Manual, baseName, isAllowed, null, isAllowed && user.IsConnected ? user : null);
        }

        private bool CanCommandContinue(BasePlayer player, IPlayer user, bool isAllowed, string[] args)
        {
            if (HandledCommandArguments(player, user, isAllowed, args))
            {
                return false;
            }

            if (!IsCopyPasteLoaded(player))
            {
                return false;
            }

            if (!isAllowed && RaidableBase.Get(RaidableType.Manual) >= config.Settings.Manual.Max)
            {
                user.Reply(m("Max Events", user.Id, "Manual", config.Settings.Manual.Max));
                return false;
            }

            if (IsSpawnOnCooldown() && !user.IsAdmin)
            {
                user.Reply(m("SpawnOnCooldown", user.Id));
                return false;
            }

            if (!isAllowed && BaseNetworkable.serverEntities.Count > 300000)
            {
                user.Reply(m("EntityCountMax", user.Id));
                return false;
            }

            return true;
        }

        private bool HandledCommandArguments(BasePlayer player, IPlayer user, bool isAllowed, string[] args)
        {
            if (args.Length == 0)
            {
                return false;
            }

            switch (args[0].ToLower())
            {
                case "despawn":
                    if (player.IsReallyValid() && isAllowed)
                    {
                        bool success = DespawnBase(player);
                        Message(player, success ? "DespawnBaseSuccess" : "DespawnBaseNoneAvailable");
                        if (success) Puts(mx("DespawnedAt", null, player.displayName, FormatGridReference(player.transform.position)));
                    }

                    return true;
                case "draw":
                    if (player.IsReallyValid())
                    {
                        DrawSpheres(player, isAllowed);
                    }
                    return true;
                case "debug":
                    {
                        if (!isAllowed) return false;
                        DebugMode = !DebugMode;
                        Queues.Messages.DebugUser = DebugMode ? user : null;
                        user.Reply(string.Format("Debug mode (v{0}): {1}", Version, DebugMode));
                        if (DebugMode)
                        {
                            user.Reply(string.Format("Scheduled Events Running: {0}", Automated._scheduledCoroutine != null));
                            user.Reply(string.Format("Maintained Events Running: {0}", Automated._maintainedCoroutine != null));
                            user.Reply(string.Format("Queues Pending: {0}", Queues.queue.Count));
                            if (Queues.Messages.Any())
                            {
                                user.Reply($"DEBUG: Last messages:");
                                Queues.Messages.PrintAll(user);
                            }
                            else user.Reply("No debug messages.");
                        }
                        return true;
                    }
                case "kill_cleanup":
                    {
                        if (args.Length == 2 && args[1] == "uid" && user.IsAdmin)
                        {
                            if (temporaryData.NID.Count > 0)
                            {
                                temporaryData.NID.ForEach(uid => BaseNetworkable.serverEntities.Find(new NetworkableId(uid)).SafelyKill());
                                user.Reply($"Kill sent for {temporaryData.NID.Count} entities.");
                            }
                            else user.Reply("0 entities to kill.");

                            return true;
                        }
                        if (!isAllowed) return false;
                        foreach (var entity in FindEntitiesOfType<BaseEntity>(player.transform.position, 100f))
                        {
                            if (entity.OwnerID == 0 && IsKillableEntity(entity))
                            {
                                entity.SafelyKill();
                            }
                        };
                        return true;
                    }
                case "despawnall":
                case "despawn_inactive":
                    {
                        if (!isAllowed) return false;
                        if (Raids.Count > 0)
                        {
                            DespawnAll(args[0].ToLower() == "despawn_inactive");
                            Puts(mx("DespawnedAll", null, user.Name));
                        }

                        return true;
                    }
                case "active":
                    {
                        if (!isAllowed) return false;
                        int count = 0;

                        foreach (var raid in Raids)
                        {
                            if (raid.intruders.Count > 0 || raid.raiders.Count > 0 || raid.ownerId.IsSteamId())
                            {
                                user.Reply($"Active raid at {raid.Location} in {FormatGridReference(raid.Location)}");
                                count++;
                            }
                        }

                        user.Reply($"{count}/{Raids.Count} active raids");
                        return true;
                    }
                case "setowner":
                case "lockraid":
                    {
                        if (args.Length >= 2 && (isAllowed || user.HasPermission("raidablebases.setowner")))
                        {
                            var target = RustCore.FindPlayer(args[1]);

                            if (target.IsReallyValid())
                            {
                                var raid = GetNearestBase(target.transform.position);

                                if (raid != null)
                                {
                                    raid.SetOwner(target);
                                    user.Reply(m("RaidLockedTo", user.Id, target.displayName)); 
                                }
                                else user.Reply(m("TargetTooFar", user.Id));
                            }
                            else user.Reply(m("TargetNotFoundId", user.Id, args[1]));
                        }
                        return true;
                    }
                case "clearowner":
                case "resetowner":
                    {
                        if (player.IsReallyValid() && (isAllowed || user.HasPermission("raidablebases.setowner")))
                        {
                            var raid = GetNearestBase(player.transform.position);

                            if (raid != null)
                            {
                                raid.ResetOwnerForced();
                                user.Reply(m("RaidOwnerCleared", user.Id));
                            }
                            else user.Reply(m("TooFar", user.Id));
                        }

                        return true;
                    }
            }

            return false;
        }

        private void DrawSpheres(BasePlayer player, bool isAllowed)
        {
            if (isAllowed || player.HasPermission("raidablebases.ddraw"))
            {
                AdminCommand(player, () =>
                {
                    foreach (var raid in Raids)
                    {
                        DrawSphere(player, 30f, Color.blue, raid.Location, raid.ProtectionRadius);
                    }
                });
            }
        }

        private void CommandToggle(IPlayer user, string command, string[] args)
        {
            if (config.Settings.Maintained.Enabled)
            {
                Automated.IsMaintainedEnabled = !Automated.IsMaintainedEnabled;
                user.Reply($"Toggled maintained events {(Automated.IsMaintainedEnabled ? "on" : "off")}");
                Automated.StartCoroutine(RaidableType.Maintained);
            }

            if (config.Settings.Schedule.Enabled)
            {
                Automated.IsScheduledEnabled = !Automated.IsScheduledEnabled;
                user.Reply($"Toggled scheduled events {(Automated.IsScheduledEnabled ? "on" : "off")}");
                Automated.StartCoroutine(RaidableType.Scheduled);
            }

            Queues.Paused = !Automated.IsScheduledEnabled && !Automated.IsMaintainedEnabled;
            user.Reply($"Toggled queue/spawn manager {(Queues.Paused ? "off" : "on")}");
        }

        private void CommandToggleType(IPlayer user, string command, string[] args)
        {
            switch (args[0].ToLower())
            {
                case "maintained":
                    {
                        Automated.IsMaintainedEnabled = config.Settings.Maintained.Enabled = !config.Settings.Maintained.Enabled;
                        Automated.StartCoroutine(RaidableType.Maintained);
                        SaveConfig();
                        user.Reply($"Toggled maintained events {(Automated.IsMaintainedEnabled ? "on" : "off")}");
                        break;
                    }
                case "scheduled":
                    {
                        Automated.IsScheduledEnabled = config.Settings.Schedule.Enabled = !config.Settings.Schedule.Enabled;
                        Automated.StartCoroutine(RaidableType.Scheduled);
                        SaveConfig();
                        user.Reply($"Toggled scheduled events {(Automated.IsScheduledEnabled ? "on" : "off")}");
                        break;
                    }
            }

            Queues.Paused = !Automated.IsScheduledEnabled && !Automated.IsMaintainedEnabled;
            user.Reply($"Toggled queue/spawn manager {(Queues.Paused ? "off" : "on")}");
        }

        private void CommandPopulate(IPlayer user, string command, string[] args)
        {
            if (args.Length == 0 || args[0] != "all")
            {
                user.Reply("You must type: rb.populate all");
                return;
            }

            var list = new List<LootItem>();

            ItemManager.GetItemDefinitions().ForEach(def =>
            {
                if (!BlacklistedItems.Contains(def.shortname))
                {
                    list.Add(new LootItem(def.shortname));
                }
            });

            list.Sort((x, y) => x.shortname.CompareTo(y.shortname));

            AddToList(RaidableMode.Normal, list);
            user.Reply("Created oxide/data/RaidableBases/Editable_Lists/Normal.json");

            AddToList(RaidableMode.Random, list);
            user.Reply("Created oxide/data/RaidableBases/Editable_Lists/Default.json");

            SaveConfig();
        }

        private void CommandToggleProfile(IPlayer user, string command, string[] args)
        {
            if (args.Length == 2)
            {
                var profileName = args[1];
                foreach (var profile in Buildings.Profiles)
                {
                    if (profile.Key.Equals(profileName, StringComparison.OrdinalIgnoreCase) || profile.Value.Options.AdditionalBases.Exists(extra => extra.Key.Equals(profileName, StringComparison.OrdinalIgnoreCase)))
                    {
                        profile.Value.Options.Enabled = !profile.Value.Options.Enabled;
                        SaveProfile(profile.Key, profile.Value.Options);
                        user.Reply(mx(profile.Value.Options.Enabled ? "ToggleProfileEnabled" : "ToggleProfileDisabled", user.Id, profile.Key));
                        break;
                    }
                }
            }
        }

        private void CommandStability(IPlayer user, string command, string[] args)
        {
            if (args.Length < 2 || args[1] != "true" && args[1] != "false")
            {
                return;
            }
            var changes = 0;
            var value = args[1];
            var sb = new StringBuilder();
            var name = args.Length == 3 ? args[2] : null;
            foreach (var profile in Buildings.Profiles.ToList())
            {
                if (!string.IsNullOrEmpty(name) && profile.Key != name)
                {
                    continue;
                }
                foreach (var extra in profile.Value.Options.AdditionalBases.ToList())
                {
                    var stability = extra.Value.Find(o => o.Key == "stability");
                    if (stability == null)
                    {
                        extra.Value.Add(new PasteOption { Key = "stability", Value = value });
                        changes++;
                        sb.AppendFormat("{0} added missing stability option for {1} to {2}", user.Name, extra.Key, value).AppendLine();
                    }
                    else if (stability.Value != value)
                    {
                        stability.Value = value;
                        changes++;
                        sb.AppendFormat("{0} changed stability option for {1} to {2}", user.Name, extra.Key, value).AppendLine();
                    }
                }
            }
            if (changes > 0)
            {
                foreach (var profile in Buildings.Profiles)
                {
                    SaveProfile(profile.Key, profile.Value.Options);
                }
                Puts("\n{0}\nChanged stability for {1} bases to {2}", sb, changes, value);
            }
            else Puts("No changes required.");
        }

        private void CommandConfig(IPlayer user, string command, string[] args)
        {
            if (!user.HasPermission("raidablebases.config") || args.Length == 0 || !arguments.Exists(str => args[0].Equals(str, StringComparison.OrdinalIgnoreCase)))
            {
                user.Reply(mx("ConfigUseFormat", user.Id, string.Join("|", arguments.ToArray())));
                return;
            }

            string arg = args[0].ToLower();

            switch (arg)
            {
                case "add": ConfigAddBase(user, args); return;
                case "remove": case "clean": ConfigRemoveBase(user, args); return;
                case "list": ConfigListBases(user); return;
                case "maintained": case "scheduled": CommandToggleType(user, command, args); return;
                case "toggle": CommandToggleProfile(user, command, args); return;
                case "stability": CommandStability(user, command, args); return;
            }
        }

        #endregion Commands

        #region Garbage

        internal Dictionary<NetworkableId, MountInfo> MountEntities { get; set; } = new Dictionary<NetworkableId, MountInfo>();
        internal Dictionary<NetworkableId, RaidEntity> RaidEntities { get; set; } = new Dictionary<NetworkableId, RaidEntity>();

        private bool KeepEntity(BaseEntity entity, bool mounts, bool structures, bool deployables)
        {
            if (!mounts && KeepMountable(entity) || entity.OwnerID.IsSteamId() && KeepPlayerEntity(entity, structures, deployables))
            {
                return true;
            }

            if (entity.IsValid())
            {
                RaidEntities.Remove(entity.net.ID);
            }

            return false;
        }

        private bool KeepPlayerEntity(BaseEntity entity, bool structures, bool deployables)
        {
            if (entity.PrefabName.Contains("building"))
            {
                if (!structures)
                {
                    return false;
                }
            }
            else if (!deployables)
            {
                if (entity is IItemContainerEntity)
                {
                    var ice = entity as IItemContainerEntity;

                    if (ice != null && ice.inventory != null)
                    {
                        DropUtil.DropItems(ice.inventory, entity.transform.position + Vector3.up);
                    }
                }

                return false;
            }

            if (entity.IsValid())
            {
                RaidEntities.Remove(entity.net.ID);
            }

            return true;
        }

        private bool KeepMountable(BaseEntity entity)
        {
            MountInfo mi;
            if (!entity.IsValid() || !MountEntities.TryGetValue(entity.net.ID, out mi) || !MountEntities.Remove(entity.net.ID))
            {
                return false;
            }

            return !mi.mountable.GetMounted().IsNull() || !InRange2D(entity.transform.position, mi.position, mi.radius);
        }

        public void RemoveHeldEntities()
        {
            foreach (var element in RaidEntities.ToList())
            {
                if (element.Key is IItemContainerEntity)
                {
                    var ice = element.Value.entity as IItemContainerEntity;

                    if (ice == null || ice.inventory == null)
                    {
                        continue;
                    }

                    RaidableBase.ClearInventory(ice.inventory);
                }
            }

            ItemManager.DoRemoves();
        }

        public void DespawnAll(bool inactiveOnly)
        {
            var entities = new List<BaseEntity>();
            int undoLimit = 1;

            foreach (RaidableBase raid in Raids.ToList())
            {
                if (raid == null || inactiveOnly && (raid.intruders.Count > 0 || raid.ownerId.IsSteamId()))
                {
                    continue;
                }

                entities.AddRange(raid.Entities);

                if (raid.Options.Setup.DespawnLimit > undoLimit)
                {
                    undoLimit = raid.Options.Setup.DespawnLimit;
                }

                raid.IsShuttingDown = true;
                raid.Despawn();
            }

            if (entities.Count > 0)
            {
                UndoLoop(entities.ToList(), undoLimit, UndoMounts, UndoStructures, UndoDeployables);
            }
        }

        public class UndoComparer : IComparer<BaseEntity>
        {
            int Evaluate(BaseEntity entity)
            {
                if (entity.ShortPrefabName.Contains("wall.external."))
                {
                    return 3;
                }
                if (entity is BuildingBlock)
                {
                    return 2;
                }
                if (!entity.HasParent())
                {
                    return 1;
                }
                return 0;
            }

            int IComparer<BaseEntity>.Compare(BaseEntity x, BaseEntity y)
            {
                return Evaluate(x).CompareTo(Evaluate(y));
            }
        }

        private UndoComparer undoComparer = new UndoComparer();

        private void KillEntity(BaseEntity entity)
        {
            KillEntity(entity, UndoMounts, UndoStructures, UndoDeployables);
        }

        private void KillEntity(BaseEntity entity, bool mounts, bool structures, bool deployables)
        {
            if (entity.IsKilled() || entity.ShortPrefabName == "item_drop_backpack" || KeepEntity(entity, mounts, structures, deployables))
            {
                return;
            }

            if (entity is IOEntity)
            {
                var io = entity as IOEntity;

                io.ClearConnections();

                if (entity is SamSite)
                {
                    var ss = entity as SamSite;

                    ss.staticRespawn = false;
                }
            }

            var uid = entity.net == null ? 0 : entity.net.ID.Value;

            entity.SafelyKill();

            if (uid != 0 && temporaryData != null && entity.IsKilled())
            {
                temporaryData.NID.Remove(uid);
            }
        }

        public void UndoLoop(List<BaseEntity> entities, int limit, bool mounts, bool structures, bool deployables, object[] hookObjects = null, int count = 0)
        {
            if (count == 0)
            {
                entities.RemoveAll(e => e.IsKilled());

                entities.Sort(undoComparer);
            }

            entities.Take(limit).ForEach(entity =>
            {
                entities.Remove(entity);

                KillEntity(entity, mounts, structures, deployables);
            });

            if (count != 0 && entities.Count != 0 && entities.Count == count)
            {
                Puts("Undo loop canceled because of infinite loop");
                entities.ForEach(e => NextTick(e.SafelyKill));
                goto done;
            }

            if (entities.Count > 0)
            {
                count = entities.Count;
                NextTick(() => UndoLoop(entities, limit, mounts, structures, deployables, hookObjects, count));
                return;
            }

        done:
            RaidEntities.RemoveAll((uid, re) => re.entity.IsKilled());
            MountEntities.RemoveAll((uid, mi) => mi.mountable.IsKilled());

            if (RaidEntities.Count == 0)
            {
                MountEntities.Clear();
            }

            if (hookObjects != null)
            {
                Interface.CallHook("OnRaidableBaseDespawned", hookObjects);
            }
        }

        #endregion Garbage

        #region Helpers

        private static void DrawText(string id, float duration, Color color, Vector3 from, object text) => DrawText(BasePlayer.Find(id), duration, color, from, text);
        private static void DrawText(BasePlayer player, float duration, Color color, Vector3 from, object text) => player?.SendConsoleCommand("ddraw.text", duration, color, from, $"<size=16>{text}</size>");
        private static void DrawLine(string id, float duration, Color color, Vector3 from, Vector3 to) => DrawLine(BasePlayer.Find(id), duration, color, from, to);
        private static void DrawLine(BasePlayer player, float duration, Color color, Vector3 from, Vector3 to) => player?.SendConsoleCommand("ddraw.line", duration, color, from, to);
        private static void DrawSphere(string id, float duration, Color color, Vector3 from, float radius) => DrawSphere(BasePlayer.Find(id), duration, color, from, radius);
        private static void DrawSphere(BasePlayer player, float duration, Color color, Vector3 from, float radius) => player?.SendConsoleCommand("ddraw.sphere", duration, color, from, radius);

        private static bool IsInstanceValid => Instance != null && !Instance.IsUnloading;

        public void UpdateAllMarkers()
        {
            foreach (var raid in Raids)
            {
                raid.UpdateMarker();
            }
        }

        private bool IsBusy(out Vector3 pastedLocation)
        {
            foreach (RaidableBase raid in Raids)
            {
                if (raid.IsDespawning || raid.IsLoading)
                {
                    pastedLocation = raid.Location;
                    return true;
                }
            }
            pastedLocation = Vector3.zero;
            return false;
        }

        public static void TryInvokeMethod(Action action)
        {
            try
            {
                action.Invoke();
            }
            catch (Exception ex)
            {
                Puts("{0} ERROR: {1}", action.Method.Name, ex);
            }
        }

        private bool IsKillableEntity(BaseEntity entity)
        {
            return entity.PrefabName.Contains("building") || _deployables.ContainsKey(entity.PrefabName) || entity is VendingMachineMapMarker || entity is MapMarkerGenericRadius || entity is SphereEntity || entity is ScientistNPC;
        }

        private static List<T> FindEntitiesOfType<T>(Vector3 a, float n, int m = -1) where T : BaseEntity
        {
            int hits = Physics.OverlapSphereNonAlloc(a, n, Vis.colBuffer, m, QueryTriggerInteraction.Collide);
            List<T> entities = new List<T>();
            for (int i = 0; i < hits; i++)
            {
                var entity = Vis.colBuffer[i]?.ToBaseEntity() as T;
                if (!entity.IsKilled() && !entities.Contains(entity)) entities.Add(entity);
                Vis.colBuffer[i] = null;
            }
            return entities;
        }

        private void CheckOceanLevel()
        {
            if (OceanLevel != WaterSystem.OceanLevel)
            {
                OceanLevel = WaterSystem.OceanLevel;

                RaidableSpawns spawns;
                if (GridController.Spawns.TryGetValue(RaidableType.Grid, out spawns))
                {
                    spawns.TryAddRange(CacheType.Submerged);
                }
            }
        }

        private void SetOnSun(bool state)
        {
            if (!config.Settings.Management.Lights)
            {
                return;
            }

            if (state)
            {
                TOD_Sky.Instance.Components.Time.OnSunrise += OnSunrise;
                TOD_Sky.Instance.Components.Time.OnSunset += OnSunset;
            }
            else
            {
                TOD_Sky.Instance.Components.Time.OnSunrise -= OnSunrise;
                TOD_Sky.Instance.Components.Time.OnSunset -= OnSunset;
            }
        }

        public static bool IsUnderground(Vector3 a) => GamePhysics.CheckSphere<TerrainCollisionTrigger>(a, 5f, 262144, QueryTriggerInteraction.Collide);

        public void InitializeSkins()
        {
            foreach (var def in ItemManager.GetItemDefinitions())
            {
                ItemModDeployable imd;
                if (def.TryGetComponent(out imd))
                {
                    _deployables[imd.entityPrefab.resourcePath] = def;
                    _definitions[def] = imd.entityPrefab.resourcePath;
                }
            }
        }

        public static void AdminCommand(BasePlayer player, Action action)
        {
            if (!player.IsAdmin && !player.IsDeveloper && player.IsFlying)
            {
                return;
            }

            bool isAdmin = player.IsAdmin;

            if (!isAdmin)
            {
                player.SetPlayerFlag(BasePlayer.PlayerFlags.IsAdmin, true);
                player.SendNetworkUpdateImmediate();
            }
            try
            {
                action();
            }
            finally
            {
                if (!isAdmin)
                {
                    player.SetPlayerFlag(BasePlayer.PlayerFlags.IsAdmin, false);
                    player.SendNetworkUpdateImmediate();
                }
            }
        }

        private static void SafelyKill(BaseEntity entity) => entity.SafelyKill();

        private bool IsHelicopter(HitInfo hitInfo)
        {
            if (hitInfo.Initiator is BaseHelicopter || hitInfo.Initiator?.ShortPrefabName == "oilfireballsmall" || hitInfo.Initiator?.ShortPrefabName == "napalm")
            {
                return true;
            }
            else if (hitInfo.WeaponPrefab?.ShortPrefabName == "rocket_heli" || hitInfo.WeaponPrefab?.ShortPrefabName == "rocket_heli_napalm")
            {
                return true;
            }
            return false;
        }

        private bool IsCopyPasteLoaded(BasePlayer player)
        {
            try
            {
                if (CopyPaste.Version >= new VersionNumber(4, 1, 32))
                {
                    return true;
                }
            }
            catch
            {
            }
            if (player.IsReallyValid())
            {
                QueueNotification(player, "InstallSupportedCopyPaste");
            }
            else Puts(mx("InstallSupportedCopyPaste"));
            return false;
        }

        private bool HasPVPDelay(ulong playerId)
        {
            return PvpDelay.ContainsKey(playerId);
        }

        private static bool IsBox(BaseEntity entity, bool inherit)
        {
            if (entity.ShortPrefabName == "box.wooden.large" || entity.ShortPrefabName == "woodbox_deployed" || entity.ShortPrefabName == "coffinstorage")
            {
                return true;
            }

            return inherit && config.Settings.Management.Inherit.Exists(entity.ShortPrefabName.Contains);
        }

        public static float GetDistance(RaidableType type)
        {
            switch (type)
            {
                case RaidableType.Maintained: return Mathf.Clamp(config.Settings.Maintained.Distance, CELL_SIZE, 9000f);
                case RaidableType.Scheduled: return Mathf.Clamp(config.Settings.Schedule.Distance, CELL_SIZE, 9000f);
                case RaidableType.None: return Mathf.Max(config.Settings.Maintained.Distance, config.Settings.Schedule.Distance);
                default: return 100f;
            }
        }

        private void AddToList(RaidableMode mode, List<LootItem> source)
        {
            List<LootItem> lootList;
            if (!Buildings.DifficultyLootLists.TryGetValue(mode, out lootList))
            {
                Buildings.DifficultyLootLists[mode] = lootList = new List<LootItem>();
            }

            foreach (var ti in source)
            {
                if (!lootList.Exists(x => x.shortname == ti.shortname))
                {
                    lootList.Add(ti);
                }
            }

            string file = $"{Name}{Path.DirectorySeparatorChar}Editable_Lists{Path.DirectorySeparatorChar}{mode}";
            Interface.Oxide.DataFileSystem.WriteObject(file, lootList);
        }

        private bool IsPVE() => TruePVE != null || NextGenPVE != null || Imperium != null;

        [HookMethod("IsPremium")]
        public bool IsPremium() => false;

        private static void NullifyDamage(HitInfo hitInfo)
        {
            if (hitInfo != null)
            {
                hitInfo.damageTypes = new DamageTypeList();
                hitInfo.DidHit = false;
                hitInfo.DoHitEffects = false;
                hitInfo.HitEntity = null;
            }
        }

        public static bool MustExclude(RaidableType type, bool allowPVP)
        {
            if (!config.Settings.Maintained.IncludePVE && type == RaidableType.Maintained && !allowPVP)
            {
                return true;
            }

            if (!config.Settings.Maintained.IncludePVP && type == RaidableType.Maintained && allowPVP)
            {
                return true;
            }

            if (!config.Settings.Schedule.IncludePVE && type == RaidableType.Scheduled && !allowPVP)
            {
                return true;
            }

            if (!config.Settings.Schedule.IncludePVP && type == RaidableType.Scheduled && allowPVP)
            {
                return true;
            }

            return false;
        }

        private bool AnyNpcs()
        {
            return Raids.Exists(x => x.npcs.Exists(npc => !npc.IsKilled()));
        }

        private void ConfigAddBase(IPlayer user, string[] args)
        {
            if (args.Length < 2)
            {
                user.Reply(mx("ConfigAddBaseSyntax", user.Id));
                return;
            }

            _sb.Clear();
            var values = new List<string>(args);
            values.RemoveAt(0);
            string profileName = values[0];

            user.Reply(mx("Adding", user.Id, string.Join(" ", values.ToArray())));

            BaseProfile profile;
            if (!Buildings.Profiles.TryGetValue(profileName, out profile))
            {
                Buildings.Profiles[profileName] = profile = new BaseProfile();
                _sb.AppendLine(mx("AddedPrimaryBase", user.Id, profileName));
            }

            foreach (string value in values)
            {
                if (!profile.Options.AdditionalBases.ContainsKey(value))
                {
                    profile.Options.AdditionalBases.Add(value, DefaultPasteOptions);
                    _sb.AppendLine(mx("AddedAdditionalBase", user.Id, value));
                }
            }

            if (_sb.Length > 0)
            {
                user.Reply(_sb.ToString());
                profile.Options.Enabled = true;
                SaveProfile(profileName, profile.Options);
                Buildings.Profiles[profileName] = profile;

                _sb.Clear();
            }
            else user.Reply(mx("EntryAlreadyExists", user.Id));

            values.Clear();
        }

        private void ConfigRemoveBase(IPlayer user, string[] args)
        {
            if (args.Length < 2)
            {
                user.Reply(mx("RemoveSyntax", user.Id));
                return;
            }

            int num = 0;
            var profiles = new Dictionary<string, BaseProfile>(Buildings.Profiles);
            var files = (string.Join(" ", args[0].ToLower() == "remove" ? args.Skip(1) : args)).Replace(", ", " ");
            var split = files.Split(' ');

            _sb.Clear();
            _sb.AppendLine(mx("RemovingAllBasesFor", user.Id, string.Join(" ", files)));

            foreach (var profile in profiles)
            {
                foreach (var element in profile.Value.Options.AdditionalBases.ToList())
                {
                    if (split.Contains(element.Key))
                    {
                        _sb.AppendLine(mx("RemovedAdditionalBase", user.Id, element.Key, profile.Key));
                        if (profile.Value.Options.AdditionalBases.Remove(element.Key)) num++;
                        SaveProfile(profile.Key, profile.Value.Options);
                    }
                }

                if (split.Contains(profile.Key))
                {
                    _sb.AppendLine(mx("RemovedPrimaryBase", user.Id, profile.Key));
                    if (Buildings.Profiles.Remove(profile.Key)) num++;
                    profile.Value.Options.Enabled = false;
                    SaveProfile(profile.Key, profile.Value.Options);
                }
            }

            _sb.AppendLine(mx("RemovedEntries", user.Id, num));
            user.Reply(_sb.ToString());
            _sb.Clear();
        }

        private void ConfigListBases(IPlayer user)
        {
            _sb.Clear();

            _sb.AppendLine();

            bool validBase = false;
            var _sb2 = new StringBuilder();

            foreach (var entry in Buildings.Profiles)
            {
                if (FileExists(entry.Key))
                {
                    _sb.Append(entry.Key);
                    validBase = true;
                }
                else _sb.Append(entry.Key).Append(mx("IsProfile", user.Id));

                if (entry.Value.Options.AdditionalBases.Count > 0)
                {
                    foreach (var ab in entry.Value.Options.AdditionalBases)
                    {
                        if (FileExists(ab.Key))
                        {
                            _sb.Append(ab.Key).Append(", ");
                            validBase = true;
                        }
                        else _sb2.Append(ab.Key).Append(mx("FileDoesNotExist", user.Id));
                    }

                    if (validBase)
                    {
                        _sb.Length -= 2;
                    }

                    _sb.AppendLine();
                    _sb.Append(_sb2);
                    _sb2.Clear();
                }

                _sb.AppendLine();
            }

            if (!validBase)
            {
                _sb.AppendLine(mx("NoBuildingsConfigured", user.Id));
            }

            user.Reply(_sb.ToString());
        }

        private static void DropOrRemoveItems(StorageContainer container, RaidableBase raid)
        {
            if (!config.Settings.Management.DropLoot.FlameTurret && container.OwnerID == 0 && container is FlameTurret)
            {
                RaidableBase.ClearInventory(container.inventory);
            }
            else if (!config.Settings.Management.DropLoot.FogMachine && container.OwnerID == 0 && container is FogMachine)
            {
                RaidableBase.ClearInventory(container.inventory);
            }
            else if (!config.Settings.Management.DropLoot.GunTrap && container.OwnerID == 0 && container is GunTrap)
            {
                RaidableBase.ClearInventory(container.inventory);
            }
            else if (!config.Settings.Management.AllowCupboardLoot && container.OwnerID == 0 && container is BuildingPrivlidge)
            {
                RaidableBase.ClearInventory(container.inventory);
            }
            else if (container.inventory.itemList.Count > 0)
            {
                var dropPosition = container.transform.position + new Vector3(0f, container is GunTrap ? 0f : container is FlameTurret ? container.bounds.extents.y : container.bounds.size.y);
                var buoyant = container is BuildingPrivlidge ? raid.Options.BuoyantPrivilege : raid.Options.BuoyantBox;
                var prefab = StringPool.Get(buoyant ? 146366564u : 545786656u);
                if (buoyant)
                {
                    //GameManager.server.FindPrefab(prefab).GetComponent<DroppedItemContainer>().maxItemCount = 48;
                }
                var drop = container.inventory.Drop(prefab, dropPosition, container.transform.rotation, 0f);
                if (raid.Options.DespawnGreyBags && container.OwnerID == 0uL)
                {
                    raid.AddEntity(drop);
                }
            }

            ItemManager.DoRemoves();
            container.Invoke(container.SafelyKill, 0.1f);
        }

        private bool IsSpawnOnCooldown()
        {
            if (Time.realtimeSinceStartup - lastSpawnRequestTime < 2f)
            {
                return true;
            }

            lastSpawnRequestTime = Time.realtimeSinceStartup;
            return false;
        }

        protected bool DespawnBase(BasePlayer player)
        {
            var raid = GetNearestBase(player.transform.position);

            if (raid == null || raid.IsLoading)
            {
                return false;
            }

            if (raid.AddNearTime <= 0f)
            {
                raid.AddNearTime = 15f;
            }

            raid.Despawn();

            return true;
        }

        private RaidableBase GetNearestBase(Vector3 target, float radius = 100f)
        {
            var values = new List<RaidableBase>();

            foreach (var x in Raids)
            {
                if (InRange2D(x.Location, target, radius))
                {
                    values.Add(x);
                }
            }

            if (values.Count == 0)
            {
                return null;
            }

            if (values.Count > 1)
            {
                values.Sort((a, b) => (a.Location - target).sqrMagnitude.CompareTo((b.Location - target).sqrMagnitude));
            }

            return values[0];
        }

        private bool IsTrueDamage(BaseEntity entity, bool isProtectedWeapon)
        {
            if (entity.IsNull())
            {
                return false;
            }

            return isProtectedWeapon || entity.skinID == 1587601905 || TrueDamage.Contains(entity.ShortPrefabName) || entity is TeslaCoil || entity is BaseTrap;
        }

        private Vector3 GetCenterLocation(Vector3 position)
        {
            for (int i = 0; i < Raids.Count; i++)
            {
                if (InRange2D(Raids[i].Location, position, Raids[i].ProtectionRadius))
                {
                    return Raids[i].Location;
                }
            }

            return Vector3.zero;
        }

        private bool HasEventEntity(BaseEntity entity)
        {
            if (entity.IsKilled()) return false;
            if (RaidableBase.Has(entity)) return true;
            if (entity is BasePlayer) return RaidableBase.Has(((BasePlayer)entity).userID);
            return false;
        }

        private bool EventTerritory(Vector3 position)
        {
            for (int i = 0; i < Raids.Count; i++)
            {
                if (InRange2D(Raids[i].Location, position, Raids[i].ProtectionRadius))
                {
                    return true;
                }
            }
            return false;
        }

        private int[] GetPlayerAmount(string userid, int mode)
        {
            foreach (var user in data.Players)
            {
                if (user.Key == userid)
                {
                    return new int[2] { user.Value.Raids, user.Value.TotalRaids };
                }
            }
            return new int[0];
        }

        private bool CanBlockOutsideDamage(RaidableBase raid, BasePlayer attacker, bool isEnabled)
        {
            return isEnabled && !InRange(attacker.transform.position, raid.Location, Mathf.Max(raid.ProtectionRadius, raid.Options.ArenaWalls.Radius));
        }

        private static bool InRange2D(Vector3 a, Vector3 b, float distance)
        {
            return (new Vector3(a.x, 0f, a.z) - new Vector3(b.x, 0f, b.z)).sqrMagnitude <= distance * distance;
        }

        private static bool InRange(Vector3 a, Vector3 b, float distance)
        {
            return (a - b).sqrMagnitude <= distance * distance;
        }

        private bool AssignTreasureHunters()
        {
            var players = data.Players.ToList().Where(x => x.Key.IsSteamId() && IsNormalUser(x.Key));

            if (!players.Exists(entry => entry.Value.Any))
            {
                return false;
            }

            foreach (var target in covalence.Players.All)
            {
                if (target.Id.HasPermission("raidablebases.th"))
                {
                    permission.RevokeUserPermission(target.Id, "raidablebases.th");
                }

                if (permission.UserHasGroup(target.Id, "raidhunter"))
                {
                    permission.RemoveUserGroup(target.Id, "raidhunter");
                }
            }

            if (config.RankedLadder.Enabled && config.RankedLadder.Amount > 0 && players.Count > 0)
            {
                AssignTreasureHunters(players);

                Puts(mx("Log Saved", null, "treasurehunters"));
            }

            return true;
        }

        private bool IsNormalUser(string userid)
        {
            if (userid.HasPermission("raidablebases.notitle"))
            {
                return false;
            }

            var user = covalence.Players.FindPlayerById(userid);

            return !(user == null || user.IsBanned);
        }

        private void AssignTreasureHunters(List<KeyValuePair<string, PlayerInfo>> players)
        {
            var ladder = new List<KeyValuePair<string, int>>();

            foreach (var entry in players)
            {
                if (entry.Value.Raids > 0) ladder.Add(new KeyValuePair<string, int>(entry.Key, entry.Value.Raids)); break;
            }

            if (ladder.Count == 0)
            {
                return;
            }

            ladder.Sort((x, y) => y.Value.CompareTo(x.Value));

            foreach (var kvp in ladder.Take(config.RankedLadder.Amount))
            {
                var p = covalence.Players.FindPlayerById(kvp.Key);

                if (p == null || p.HasPermission("raidablebases.ladder.exclude"))
                {
                    continue;
                }

                permission.GrantUserPermission(p.Id, "raidablebases.th", this);
                permission.AddUserGroup(p.Id, "raidhunter");

                string message = mx("Log Stolen", null, p.Name, p.Id, kvp.Value);

                LogToFile("treasurehunters", $"{DateTime.Now} : {message}", this, true);
                Puts(mx("Log Granted", null, p.Name, p.Id, "raidablebases.th", "raidhunter"));
            }
        }

        public static string FormatGridReference(Vector3 position)
        {
            if (config.Settings.ShowXZ)
            {
                return string.Format("{0} ({1} {2})", PositionToGrid(position), position.x.ToString("N2"), position.z.ToString("N2"));
            }

            return PositionToGrid(position);
        }

        private static string PositionToGrid(Vector3 position) => PhoneController.PositionToGridCoord(position);

        private static string FormatTime(double seconds, string id = null)
        {
            if (seconds < 0)
            {
                return "0s";
            }

            var ts = TimeSpan.FromSeconds(seconds);
            string format = mx("TimeFormat", id);

            if (format == "TimeFormat")
            {
                format = "{0:D2}h {1:D2}m {2:D2}s";
            }

            return string.Format(format, ts.Hours, ts.Minutes, ts.Seconds);
        }

        #endregion

        #region Data files

        private bool ProfilesExists()
        {
            try
            {
                Interface.Oxide.DataFileSystem.GetFiles($"{Name}{Path.DirectorySeparatorChar}Profiles");
            }
            catch
            {
                return false;
            }

            return true;
        }

        private void CreateDefaultFiles()
        {
            if (ProfilesExists())
            {
                return;
            }

            Interface.Oxide.DataFileSystem.GetDatafile($"{Name}{Path.DirectorySeparatorChar}Profiles{Path.DirectorySeparatorChar}_emptyfile");

            foreach (var building in DefaultBuildingOptions)
            {
                string filename = $"{Name}{Path.DirectorySeparatorChar}Profiles{Path.DirectorySeparatorChar}{building.Key}";

                if (!Interface.Oxide.DataFileSystem.ExistsDatafile(filename))
                {
                    SaveProfile(building.Key, building.Value);
                }
            }

            string lootFile = $"{Name}{Path.DirectorySeparatorChar}Default_Loot";

            if (!Interface.Oxide.DataFileSystem.ExistsDatafile(lootFile))
            {
                Interface.Oxide.DataFileSystem.WriteObject(lootFile, DefaultLoot);
            }
        }

        protected void VerifyProfiles()
        {
            bool allowPVP = Buildings.Profiles.Values.Exists(profile => profile.Options.AllowPVP);
            bool allowPVE = Buildings.Profiles.Values.Exists(profile => !profile.Options.AllowPVP);

            if (config.Settings.Maintained.Enabled)
            {
                if (allowPVP && !config.Settings.Maintained.IncludePVP && !allowPVE)
                {
                    Puts("Invalid configuration detected: Maintained Events -> Include PVP Bases is set false, and all profiles have Allow PVP enabled. Therefore no bases can spawn for Maintained Events. The ideal configuration is for Include PVP Bases to be set true, and Convert PVP To PVE to be set true.");
                }

                if (allowPVE && !config.Settings.Maintained.IncludePVE && !allowPVP)
                {
                    Puts("Invalid configuration detected: Maintained Events -> Include PVE Bases is set false, and all profiles have Allow PVP disabled. Therefore no bases can spawn for Maintained Events. The ideal configuration is for Include PVE Bases to be set true, and Convert PVE To PVP to be set true.");
                }
            }

            if (config.Settings.Schedule.Enabled)
            {
                if (allowPVP && !config.Settings.Schedule.IncludePVP && !allowPVE)
                {
                    Puts("Invalid configuration detected: Scheduled Events -> Include PVP Bases is set false, and all profiles have Allow PVP enabled. Therefore no bases can spawn for Scheduled Events. The ideal configuration is for Include PVP Bases to be set true, and Convert PVP To PVE to be set true.");
                }

                if (allowPVE && !config.Settings.Schedule.IncludePVE && !allowPVP)
                {
                    Puts("Invalid configuration detected: Scheduled Events -> Include PVE Bases is set false, and all profiles have Allow PVP disabled. Therefore no bases can spawn for Scheduled Events. The ideal configuration is for Include PVE Bases to be set true, and Convert PVE To PVP to be set true.");
                }
            }
        }

        protected IEnumerator LoadProfiles()
        {
            string folder = $"{Name}{Path.DirectorySeparatorChar}Profiles";
            string[] files;

            try
            {
                files = Interface.Oxide.DataFileSystem.GetFiles(folder);
            }
            catch (UnauthorizedAccessException ex)
            {
                Puts("{0}", ex);
                yield break;
            }

            foreach (string file in files)
            {
                yield return CoroutineEx.waitForFixedUpdate;

                string profileName = file;

                try
                {
                    if (file.Contains("_empty"))
                    {
                        continue;
                    }

                    int index = file.LastIndexOf(Path.DirectorySeparatorChar) + 1;

                    profileName = Oxide.Core.Utility.GetFileNameWithoutExtension(file.Substring(index, file.Length - index));
                    
                    string fullName = $"{folder}{Path.DirectorySeparatorChar}{profileName}";

                    var options = Interface.Oxide.DataFileSystem.ReadObject<BuildingOptions>(fullName);

                    if (options == null)
                    {
                        continue;
                    }

                    if (options.NPC.SpawnAmountMurderers == -9)
                    {
                        options.NPC.SpawnAmountMurderers = 2;
                    }

                    if (options.NPC.SpawnMinAmountMurderers == -9)
                    {
                        options.NPC.SpawnMinAmountMurderers = 2;
                    }

                    if (options.NPC.SpawnAmountScientists == -9)
                    {
                        options.NPC.SpawnAmountScientists = 2;
                    }

                    if (options.NPC.SpawnMinAmountScientists == -9)
                    {
                        options.NPC.SpawnMinAmountScientists = 2;
                    }

                    if (options.AdditionalBases == null)
                    {
                        options.AdditionalBases = new Dictionary<string, List<PasteOption>>();
                    }

                    if (options.NPC.Accuracy == null)
                    {
                        options.NPC.Accuracy = new NpcSettingsAccuracyDifficulty(25f);
                    }

                    if (options.Setup.DespawnLimit > despawnLimit)
                    {
                        despawnLimit = options.Setup.DespawnLimit;
                    }

                    if (options.ProtectionRadiusObsolete.HasValue)
                    {
                        options.ProtectionRadii.Manual = options.ProtectionRadii.Maintained = options.ProtectionRadii.Scheduled = options.ProtectionRadiusObsolete.Value;
                        options.ProtectionRadiusObsolete = null;
                    }

                    Buildings.Profiles[profileName] = new BaseProfile(options, profileName);
                }
                catch (JsonSerializationException ex)
                {
                    continue;
                }
                catch (Exception ex)
                {
                    Puts("{0}\n{1}", file, ex);
                }
            }

            foreach (var profile in Buildings.Profiles)
            {
                //if (profile.Value.Options.Eco != null)
                //{
                //    AbortInitialization();
                //    yield break;
                //}
                SaveProfile(profile.Key, profile.Value.Options);
                yield return CoroutineEx.waitForFixedUpdate;
            }

            yield return LoadBaseTables();

            VerifyProfiles();
            LoadImportedSkins();
        }

        private void LoadImportedSkins()
        {
            string skinsFilename = $"{Name}{Path.DirectorySeparatorChar}ImportedWorkshopSkins";

            try
            {
                ImportedWorkshopSkins = Interface.Oxide.DataFileSystem.ReadObject<SkinSettingsImportedWorkshop>(skinsFilename);
            }
            catch (JsonException ex)
            {
                UnityEngine.Debug.LogException(ex);
                ImportedWorkshopSkins = new SkinSettingsImportedWorkshop();
            }
            finally
            {
                if (ImportedWorkshopSkins == null)
                {
                    Interface.Oxide.DataFileSystem.WriteObject(skinsFilename, ImportedWorkshopSkins = new SkinSettingsImportedWorkshop());
                }
            }
        }

        protected void SaveProfile(string key, BuildingOptions options)
        {
            Interface.Oxide.DataFileSystem.WriteObject($"{Name}{Path.DirectorySeparatorChar}Profiles{Path.DirectorySeparatorChar}{key}", options);
        }

        protected IEnumerator LoadTables()
        {
            Buildings = new BuildingTables();
            _sb.Length = 0;
            _sb.AppendLine("-");

            var modes = new List<RaidableMode>();
            modes.Add(RaidableMode.Normal);
            modes.Add(RaidableMode.Random);

            foreach (RaidableMode mode in modes)
            {
                string file = mode == RaidableMode.Random ? $"{Name}{Path.DirectorySeparatorChar}Default_Loot" : $"{Name}{Path.DirectorySeparatorChar}Difficulty_Loot{Path.DirectorySeparatorChar}{mode}";
                var lootTable = Buildings.DifficultyLootLists[mode] = GetTable(file);
                LoadTable(file, lootTable);
                yield return CoroutineEx.waitForFixedUpdate;
            }

            foreach (DayOfWeek day in Enum.GetValues(typeof(DayOfWeek)))
            {
                string file = $"{Name}{Path.DirectorySeparatorChar}Weekday_Loot{Path.DirectorySeparatorChar}{day}";
                var lootTable = Buildings.WeekdayLootLists[day] = GetTable(file);
                LoadTable(file, lootTable);
                yield return CoroutineEx.waitForFixedUpdate;
            }
        }

        protected IEnumerator LoadBaseTables()
        {
            foreach (var entry in Buildings.Profiles)
            {
                string file = $"{Name}{Path.DirectorySeparatorChar}Base_Loot{Path.DirectorySeparatorChar}{entry.Key}";
                LoadTable(file, BaseLootList = GetTable(file));
                if (BaseLootList.Count > 0) break;
                yield return CoroutineEx.waitForFixedUpdate;
            }

            Interface.Oxide.LogInfo("{0}", _sb.ToString());
            _sb.Clear();
        }

        private void LoadTable(string file, List<LootItem> lootList)
        {
            if (lootList.Count == 0)
            {
                return;
            }

            if (lootList.All(ti => ti.probability == 0f))
            {
                lootList.ForEach(ti => ti.probability = 1f);
            }

            if (lootList.All(ti => ti.stacksize == 0))
            {
                lootList.ForEach(ti => ti.stacksize = -1);
            }

            lootList.ToList().ForEach(ti =>
            {
                if (ti.amount < ti.amountMin)
                {
                    ti.amount = ti.amountMin;
                }
                if (ti.shortname == "chocholate")
                {
                    ti.shortname = "chocolate";
                }
            });

            Interface.Oxide.DataFileSystem.WriteObject(file, lootList);

            lootList.RemoveAll(ti => ti.amount == 0 || BlacklistedItems.Contains(ti.shortname));

            if (lootList.Count > 0)
            {
                _sb.AppendLine($"Loaded {lootList.Count} items from {file}");
            }
        }

        private List<string> BlacklistedItems = new List<string> { "ammo.snowballgun", "habrepair", "minihelicopter.repair", "scraptransport.repair", "vehicle.chassis", "vehicle.chassis.4mod", "vehicle.chassis.2mod", "vehicle.module" };

        private List<LootItem> GetTable(string file)
        {
            var lootList = new List<LootItem>();

            try
            {
                lootList = Interface.Oxide.DataFileSystem.ReadObject<List<LootItem>>(file);
            }
            catch (JsonReaderException ex)
            {
                Puts("Json error in loot table file: {0}\n\n\nUse a json validator: www.jsonlint.com\n\n\n{1}", file, ex);
            }

            if (lootList == null)
            {
                return new List<LootItem>();
            }

            return lootList.Where(ti => ti != null);
        }

        #endregion

        #region Configuration

        protected override void LoadDefaultMessages()
        {
            lang.RegisterMessages(new Dictionary<string, string>
            {
                ["No Permission"] = "You do not have permission to use this command.",
                ["Building is blocked for spawns!"] = "<color=#FF0000>Building is blocked until a raidable base spawns!</color>",
                ["Building is blocked!"] = "<color=#FF0000>Building is blocked near raidable bases!</color>",
                ["Ladders are blocked!"] = "<color=#FF0000>Ladders are blocked in raidable bases!</color>",
                ["Barricades are blocked!"] = "<color=#FF0000>Barricades are blocked in raidable bases!</color>",
                ["Cupboards are blocked!"] = "<color=#FF0000>Tool cupboards are blocked in raidable bases!</color>",
                ["Ladders Require Building Privilege!"] = "<color=#FF0000>You need building privilege to place ladders!</color>",
                ["Profile Not Enabled"] = "This profile is not enabled: <color=#FF0000>{0}</color>.",
                ["Max Events"] = "Maximum limit of {0} events (<color=#FF0000>{1}</color>) has been reached!",
                ["Manual Event Failed"] = "Event failed to start! Unable to obtain a valid position. Please try again.",
                ["Help"] = "/{0} <tp> - start a manual event, and teleport to the position if TP argument is specified and you are an admin.",
                ["RaidOpenMessage"] = "<color=#C0C0C0>A {0} raidable base event has opened at <color=#FFFF00>{1}</color>! You are <color=#FFA500>{2}m</color> away. [{3}]</color>",
                ["RaidOpenNoMapMessage"] = "<color=#C0C0C0>A {0} raidable base event has opened! You are <color=#FFA500>{1}m</color> away. [{2}]</color>",
                ["Next"] = "<color=#C0C0C0>No events are open. Next event in <color=#FFFF00>{0}</color></color>",
                ["Wins"] = "<color=#C0C0C0>You have looted <color=#FFFF00>{0}</color> raid bases! View the ladder using <color=#FFA500>/{1} ladder</color> or <color=#FFA500>/{1} lifetime</color></color>",
                ["RaidMessage"] = "Raidable Base {0}m [{1} players]",
                ["RankedLadder"] = "<color=#FFFF00>[ Top {0} {1} (This Wipe) ]</color>:",
                ["RankedTotal"] = "<color=#FFFF00>[ Top {0} {1} (Lifetime) ]</color>:",
                ["Ladder Insufficient Players"] = "<color=#FFFF00>No players are on the ladder yet!</color>",
                ["Next Automated Raid"] = "Next automated raid in {0} at {1}",
                ["Not Enough Online"] = "Not enough players online ({0} minimum)",
                ["Too Many Online"] = "Too many players online ({0} maximum)",
                ["Raid Base Distance"] = "<color=#C0C0C0>Raidable Base <color=#FFA500>{0}m</color>",
                ["Destroyed Raid"] = "Destroyed a left over raid base at {0}",
                ["Indestructible"] = "<color=#FF0000>Treasure chests are indestructible!</color>",
                ["Log Stolen"] = "{0} ({1}) Raids {2}",
                ["Log Granted"] = "Granted {0} ({1}) permission {2} for group {3}",
                ["Log Saved"] = "Raid Hunters have been logged to: {0}",
                ["Prefix"] = "[ <color=#406B35>Raidable Bases</color> ] ",
                ["RestartDetected"] = "Restart detected. Next event in {0} minutes.",
                ["EconomicsDeposit"] = "You have received <color=#FFFF00>${0}</color> for stealing the treasure!",
                ["EconomicsWithdraw"] = "You have paid <color=#FFFF00>${0}</color> for a raidable base!",
                ["EconomicsWithdrawReset"] = "<color=#FFFF00>${0}</color> was paid for your cooldown reset!",
                ["EconomicsWithdrawGift"] = "{0} has paid <color=#FFFF00>${1}</color> for your raidable base!",
                ["EconomicsWithdrawFailed"] = "You do not have <color=#FFFF00>${0}</color> for a raidable base!",
                ["ServerRewardPoints"] = "You have received <color=#FFFF00>{0} RP</color> for stealing the treasure!",
                ["ServerRewardPointsTaken"] = "You have paid <color=#FFFF00>{0} RP</color> for a raidable base!",
                ["ServerRewardPointsTakenReset"] = "<color=#FFFF00>{0} RP</color> was paid for your cooldown reset!",
                ["ServerRewardPointsGift"] = "{0} has paid <color=#FFFF00>{1} RP</color> for your raidable base!",
                ["ServerRewardPointsFailed"] = "You do not have <color=#FFFF00>{0} RP</color> for a raidable base!",
                ["SkillTreeXP"] = "You have received <color=#FFFF00>{0} XP</color> for stealing the treasure!",
                ["InvalidItem"] = "Invalid item shortname: {0}. Use /{1} additem <shortname> <amount> [skin]",
                ["AddedItem"] = "Added item: {0} amount: {1}, skin: {2}",
                ["CustomPositionSet"] = "Custom event spawn location set to: {0}",
                ["CustomPositionRemoved"] = "Custom event spawn location removed.",
                ["OpenedEvents"] = "Opened {0}/{1} events.",
                ["OnPlayerEntered"] = "<color=#FF0000>You have entered a raidable PVP base!</color>",
                ["OnPlayerEnteredPVE"] = "<color=#FF0000>You have entered a raidable PVE base!</color>",
                ["OnPlayerEntryRejected"] = "<color=#FF0000>You cannot enter an event that does not belong to you!</color>",
                ["OnLockedToRaid"] = "<color=#FF0000>You are now locked to this base.</color>",
                ["OnFirstPlayerEntered"] = "<color=#FFFF00>{0}</color> is the first to enter the raidable base at <color=#FFFF00>{1}</color>",
                ["OnChestOpened"] = "<color=#FFFF00>{0}</color> is the first to see the loot at <color=#FFFF00>{1}</color>!</color>",
                ["OnRaidFinished"] = "The raid at <color=#FFFF00>{0}</color> has been unlocked!",
                ["CannotBeMounted"] = "You cannot loot the treasure while mounted!",
                ["CannotTeleport"] = "You are not allowed to teleport from this event.",
                ["CannotRemove"] = "You are not allowed to remove entities from this event.",
                ["MustBeAuthorized"] = "You must have building privilege to access this treasure!",
                ["OwnerLocked"] = "This treasure belongs to someone else!",
                ["CannotFindPosition"] = "Could not find a random position!",
                ["PasteOnCooldown"] = "Paste is on cooldown!",
                ["SpawnOnCooldown"] = "Try again, a manual spawn was already requested.",
                ["ThievesDespawn"] = "<color=#FFFF00>The {0} base at <color=#FFFF00>{1}</color> has been despawned by <color=#FFFF00>{2}</color>!</color>",
                ["Thieves"] = "<color=#FFFF00>The {0} base at <color=#FFFF00>{1}</color> has been raided by <color=#FFFF00>{2}</color>!</color>",
                ["TargetNotFoundId"] = "<color=#FFFF00>Target {0} not found, or not online.</color>",
                ["TargetNotFoundNoId"] = "<color=#FFFF00>No steamid provided.</color>",
                ["BaseQueued"] = "<color=#FFFF00>Your base will spawn when a position is found. It is currently at position {0} in the queue.</color>",
                ["DestroyingBaseAt"] = "<color=#C0C0C0>Destroying raid base at <color=#FFFF00>{0}</color> in <color=#FFFF00>{1}</color> minutes!</color>",
                ["PasteIsBlocked"] = "You cannot start a raid base event there!",
                ["LookElsewhere"] = "Unable to find a position; look elsewhere.",
                ["BuildingNotConfigured"] = "You cannot spawn a base that is not configured.",
                ["NoBuildingsConfigured"] = "No valid buildings have been configured.",
                ["DespawnBaseSuccess"] = "<color=#C0C0C0>Despawning the nearest raid base to you!</color>",
                ["DespawnedAt"] = "{0} despawned a base manually at {1}",
                ["DespawnedAll"] = "{0} despawned all bases manually",
                ["Normal"] = "normal",
                ["DespawnBaseNoneAvailable"] = "<color=#C0C0C0>You must be within 100m of a raid base to despawn it.</color>",
                ["GridIsLoading"] = "The grid is loading; please wait until it has finished.",
                ["GridIsLoadingFormatted"] = "Grid is loading. The process has taken {0} seconds so far with {1} locations added on the grid.",
                ["TooPowerful"] = "<color=#FF0000>This place is guarded by a powerful spirit. You sheath your wand in fear!</color>",
                ["TooPowerfulDrop"] = "<color=#FF0000>This place is guarded by a powerful spirit. You drop your wand in fear!</color>",
                ["InstallSupportedCopyPaste"] = "You must update your version of CopyPaste to 4.1.32 or higher!",
                ["DoomAndGloom"] = "<color=#FF0000>You have left a {0} zone and can be attacked for another {1} seconds!</color>",
                ["NoConfiguredLoot"] = "Error: No loot found in the config!",
                ["NoContainersFound"] = "Error: No usable containers found for {0} @ {1}!",
                ["NoEntitiesFound"] = "Error: No entities found at {0} @ {1}!",
                ["NoBoxesFound"] = "Error: No usable boxes found for {0} @ {1}!",
                ["NoLootSpawned"] = "Error: No loot was spawned!",
                ["LoadedManual"] = "Loaded {0} manual spawns.",
                ["LoadedMaintained"] = "Loaded {0} maintained spawns.",
                ["LoadedScheduled"] = "Loaded {0} scheduled spawns.",
                ["Initialized Grid"] = "Grid initialization completed in {0} seconds and {1} milliseconds on a {2} size map with {3} potential points.",
                ["Initialized Grid Sea"] = "{0} potential points are on the seabed grid.",
                ["EntityCountMax"] = "Command disabled due to entity count being greater than 300k",
                ["NotifyPlayerFormat"] = "<color=#ADD8E6>{rank}</color>. <color=#C0C0C0>{name}</color> (raided <color=#FFFF00>{value}</color> bases for <color=#FFFF00>{points}</color> points)",
                ["ConfigUseFormat"] = "Use: rb.config <{0}> [base] [subset]",
                ["ConfigAddBaseSyntax"] = "Use: rb.config add nivex1 nivex4 nivex5 nivex6",
                ["FileDoesNotExist"] = " > This file does not exist\n",
                ["IsProfile"] = " > Profile\n",
                ["ListingAll"] = "Listing all primary bases and their subsets:",
                ["PrimaryBase"] = "Primary Base: ",
                ["AdditionalBase"] = "Additional Base: ",
                ["NoValidBuilingsWarning"] = "No valid buildings are configured with a valid file that exists. Did you configure valid files and reload the plugin?",
                ["Adding"] = "Adding: {0}",
                ["AddedPrimaryBase"] = "Added Primary Base: {0}",
                ["AddedAdditionalBase"] = "Added Additional Base: {0}",
                ["EntryAlreadyExists"] = "That entry already exists.",
                ["RemoveSyntax"] = "Use: rb.config remove nivex1",
                ["RemovingAllBasesFor"] = "\nRemoving all bases for: {0}",
                ["RemovedPrimaryBase"] = "Removed primary base: {0}",
                ["RemovedAdditionalBase"] = "Removed additional base {0} from primary base {1}",
                ["RemovedEntries"] = "Removed {0} entries",
                ["ToggleProfileEnabled"] = "{0} profile is now enabled.",
                ["ToggleProfileDisabled"] = "{0} profile is now disabled.",
                ["LockedOut"] = "You are locked out from {0} raids for {1}",
                ["PVPFlag"] = "[<color=#FF0000>PVP</color>] ",
                ["PVEFlag"] = "[<color=#008000>PVE</color>] ",
                ["PVP ZONE"] = "PVP ZONE",
                ["PVE ZONE"] = "PVE ZONE",
                ["OnPlayerExit"] = "<color=#FF0000>You have left a raidable PVP base!</color>",
                ["OnPlayerExitPVE"] = "<color=#FF0000>You have left a raidable PVE base!</color>",
                ["PasteIsBlockedStandAway"] = "You cannot start a raid base event there because you are too close to the spawn. Either move or use noclip.",
                ["ReloadConfig"] = "Reloading config...",
                ["ReloadMaintainCo"] = "Stopped maintain coroutine.",
                ["ReloadScheduleCo"] = "Stopped schedule coroutine.",
                ["ReloadSpawnerCo"] = "Stopped spawner coroutine.",
                ["ReloadInit"] = "Initializing...",
                ["YourCorpse"] = "Your Corpse",
                ["EjectedYourCorpse"] = "Your corpse has been ejected from your raid.",
                ["NotAllowed"] = "<color=#FF0000>That action is not allowed in this zone.</color>",
                ["AllowedZones"] = "Allowed spawn points in {0} zones.",
                ["BlockedZones"] = "Blocked spawn points in {0} zones.",
                ["UI Format"] = "{0} - Loot Remaining: {1} [Despawn in {2} mins]",
                ["UI FormatContainers"] = "{0} - Loot Remaining: {1}",
                ["UI FormatMinutes"] = "{0} [Despawn in {1} mins]",
                ["UIFormatLockoutMinutes"] = "{0}m",
                ["HoggingFinishYourRaid"] = "<color=#FF0000>You must finish your last raid at {0} before joining another.</color>",
                ["HoggingFinishYourRaidClan"] = "<color=#FF0000>Your clan mate `{0}` must finish their last raid at {1}.</color>",
                ["HoggingFinishYourRaidTeam"] = "<color=#FF0000>Your team mate `{0}` must finish their last raid at {1}.</color>",
                ["HoggingFinishYourRaidFriend"] = "<color=#FF0000>Your friend `{0}` must finish their last raid at {1}.</color>",
                ["TimeFormat"] = "{0:D2}h {1:D2}m {2:D2}s",
                ["TargetTooFar"] = "Your target is not close enough to a raid.",
                ["TooFar"] = "You are not close enough to a raid.",
                ["RaidLockedTo"] = "Raid has been locked to: {0}",
                ["RaidOwnerCleared"] = "Raid owner has been cleared.",
                ["TooCloseToABuilding"] = "Too close to another building",
                ["CommandNotAllowed"] = "You are not allowed to use this command right now.",
                ["MapMarkerOrderWithMode"] = "{0}{1} {2}{3}",
                ["MapMarkerOrderWithoutMode"] = "{0}{1}{2}",
                ["BannedAdmin"] = "You have the raidablebases.banned permission and as a result are banned from these events.",
                ["Banned"] = "You are banned from these events.",
                ["NoMountedDamageTo"] = "You cannot damage mounts!",
                ["NoMountedDamageFrom"] = "You cannot do damage while mounted to this!",
                ["NoDamageFromOutsideToBaseInside"] = "You must be inside of the event to damage the base!",
                ["NoDamageToEnemyBase"] = "You are not allowed to damage another players event!",
                ["NoDamageToBoxes"] = "This box is immune to damage.",
                ["None"] = "None",
                ["You"] = "You",
                ["Enemy"] = "Enemy",
                ["RP"] = "RP",
                ["Ally"] = "Ally",
                ["Owner"] = "Owner:",
                ["OwnerFormat"] = "OWNER: <color={0}>{1}</color> ",
                ["Active"] = "Active",
                ["Inactive"] = "Inactive",
                ["InactiveTimeLeft"] = " [Inactive in {0} mins]",
                ["Status:"] = "YOUR STATUS: <color={0}>{1}</color>{2}",
                ["Claimed"] = "(Claimed)",
                ["Refunded"] = "You have been refunded: {0}",
                ["TryAgain"] = "Try again at a different location.",
                ["Elevator Health"] = "Elevator Health:",
                ["Elevator Green Card"] = "Elevator access requires a green access card!",
                ["Elevator Blue Card"] = "Elevator access requires a blue access card!",
                ["Elevator Red Card"] = "Elevator access requires a red access card!",
                ["Elevator Special Card"] = "Elevator access requires a special access card!",
                ["Elevator Privileges"] = "Elevator access requires building privileges!",
                ["Invite Usage"] = "/{0} invite <name>",
                ["Invite Ownership Error"] = "You must have ownership of a raid to invite someone.",
                ["Invite Success"] = "You have invited {0} to join your raid.",
                ["Invite Allowed"] = "You have been allowed to join the raid owned by {0}.",
                ["No Reward: Flying"] = "You cannot earn a reward while flying.",
                ["No Reward: Vanished"] = "You cannot earn a reward while vanished.",
                ["No Reward: Inactive"] = "You cannot earn a reward while inactive.",
                ["No Reward: Admin"] = "Administrators cannot earn rewards.",
                ["No Reward: Not Owner"] = "You must be the owner of the raid to be eligible.",
                ["No Reward: Not Ally"] = "You must be the owner or an ally of the raid to be eligible.",
                ["No Reward: Not A Participant"] = "You must be a participant of the raid to be eligible.",
                ["NoFauxAdmin"] = "You may not use admin cheats in this area.",
                ["MLRS Target Denied"] = "You are not allowed to target this location!",
            }, this, "en");
        }

        public static void Message(BasePlayer player, string key, params object[] args)
        {
            if (player.IsReallyValid())
            {
                QueueNotification(player, key, args);
            }
        }

        public static string m(string key, string id = null, params object[] args)
        {
            if (id == null || id == "server_console")
            {
                return mx(key, id, args);
            }

            if (Instance == null)
            {
                return key;
            }

            _sb2.Length = 0;

            if (config.EventMessages.Prefix)
            {
                _sb2.Append(Instance.lang.GetMessage("Prefix", Instance, id));
            }

            string message = Instance.lang.GetMessage(key, Instance, id);

            if (string.IsNullOrEmpty(message))
            {
                return string.Empty;
            }

            _sb2.Append(message);

            return args.Length > 0 ? string.Format(_sb2.ToString(), args) : _sb2.ToString();
        }

        public static string mx(string key, string id = null, params object[] args)
        {
            if (Instance == null)
            {
                return key;
            }

            _sb2.Length = 0;

            string message = Instance.lang.GetMessage(key, Instance, id);

            if (string.IsNullOrEmpty(message))
            {
                return string.Empty;
            }

            _sb2.Append(id == null || id == "server_console" ? rf(message) : message);

            return args.Length > 0 ? string.Format(_sb2.ToString(), args) : _sb2.ToString();
        }

        public static string rf(string source) => source.Contains(">") ? Regex.Replace(source, "<.*?>", string.Empty) : source;

        public class Notification
        {
            public BasePlayer player;
            public string messageEx;
        }

        private Dictionary<ulong, List<Notification>> _notifications = new Dictionary<ulong, List<Notification>>();

        private void CheckNotifications()
        {
            if (_notifications.Count > 0)
            {
                foreach (var entry in _notifications.ToList())
                {
                    var notification = entry.Value.ElementAt(0);

                    SendNotification(notification);

                    entry.Value.Remove(notification);

                    if (entry.Value.Count == 0)
                    {
                        _notifications.Remove(entry.Key);
                    }
                }
            }
        }

        private static void QueueNotification(BasePlayer player, string key, params object[] args)
        {
            if (!player.IsReallyConnected())
            {
                return;
            }

            string message = m(key, player.UserIDString, args);

            if (string.IsNullOrEmpty(message))
            {
                return;
            }

            if (config.EventMessages.Message)
            {
                Instance.Player.Message(player, message, config.Settings.ChatID);
            }

            if (config.GUIAnnouncement.Enabled || config.UI.AA.Enabled || config.EventMessages.NotifyType != -1)
            {
                string messageEx = mx(key, player.UserIDString, args);

                List<Notification> notifications;
                if (!Instance._notifications.TryGetValue(player.userID, out notifications))
                {
                    Instance._notifications[player.userID] = notifications = new List<Notification>();
                }

                notifications.Add(new Notification
                {
                    player = player,
                    messageEx = messageEx
                });
            }
        }

        private static void SendNotification(Notification notification)
        {
            if (!notification.player.IsReallyConnected())
            {
                return;
            }

            if (config.GUIAnnouncement.Enabled && Instance.GUIAnnouncements.CanCall())
            {
                Instance.GUIAnnouncements?.Call("CreateAnnouncement", notification.messageEx, config.GUIAnnouncement.TintColor, config.GUIAnnouncement.TextColor, notification.player);
            }

            if (config.UI.AA.Enabled && Instance.AdvancedAlerts.CanCall())
            {
                Instance.AdvancedAlerts?.Call("SpawnAlert", notification.player, "hook", notification.messageEx, config.UI.AA.AnchorMin, config.UI.AA.AnchorMax, config.UI.AA.Time);
            }

            if (config.EventMessages.NotifyType != -1 && Instance.Notify.CanCall())
            {
                Instance.Notify?.Call("SendNotify", notification.player, config.EventMessages.NotifyType, notification.messageEx);
            }
        }

        protected new static void Puts(string format, params object[] args)
        {
            if (!string.IsNullOrEmpty(format))
            {
                Interface.Oxide.LogInfo("[{0}] {1}", Name, (args.Length != 0) ? string.Format(format, args) : format);
            }
        }

        private static Configuration config;

        private static Dictionary<string, List<ulong>> DefaultImportedSkins
        {
            get
            {
                return new Dictionary<string, List<ulong>>
                {
                    ["jacket.snow"] = new List<ulong> { 785868744, 939797621 },
                    ["knife.bone"] = new List<ulong> { 1228176194, 2038837066 }
                };
            }
        }

        private static List<PasteOption> DefaultPasteOptions
        {
            get
            {
                return new List<PasteOption>
                {
                    new PasteOption() { Key = "stability", Value = "false" },
                    new PasteOption() { Key = "autoheight", Value = "false" },
                    new PasteOption() { Key = "height", Value = "1.0" },
                };
            }
        }

        private static Dictionary<string, BuildingOptions> DefaultBuildingOptions
        {
            get
            {
                return new Dictionary<string, BuildingOptions>()
                {
                    ["RaidBases"] = new BuildingOptions("RaidBase1", "RaidBase2", "RaidBase3", "RaidBase4", "RaidBase5")
                    {
                        NPC = new NpcSettings(25.0)
                    }
                };
            }
        }

        private static List<LootItem> DefaultLoot
        {
            get
            {
                return new List<LootItem>
                {
                    new LootItem("ammo.pistol", 40, 40),
                    new LootItem("ammo.pistol.fire", 40, 40),
                    new LootItem("ammo.pistol.hv", 40, 40),
                    new LootItem("ammo.rifle", 60, 60),
                    new LootItem("ammo.rifle.explosive", 60, 60),
                    new LootItem("ammo.rifle.hv", 60, 60),
                    new LootItem("ammo.rifle.incendiary", 60, 60),
                    new LootItem("ammo.shotgun", 24, 24),
                    new LootItem("ammo.shotgun.slug", 40, 40),
                    new LootItem("surveycharge", 20, 20),
                    new LootItem("bucket.helmet", 1, 1),
                    new LootItem("cctv.camera", 1, 1),
                    new LootItem("coffeecan.helmet", 1, 1),
                    new LootItem("explosive.timed", 1, 1),
                    new LootItem("metal.facemask", 1, 1),
                    new LootItem("metal.plate.torso", 1, 1),
                    new LootItem("mining.quarry", 1, 1),
                    new LootItem("pistol.m92", 1, 1),
                    new LootItem("rifle.ak", 1, 1),
                    new LootItem("rifle.bolt", 1, 1),
                    new LootItem("rifle.lr300", 1, 1),
                    new LootItem("shotgun.pump", 1, 1),
                    new LootItem("shotgun.spas12", 1, 1),
                    new LootItem("smg.2", 1, 1),
                    new LootItem("smg.mp5", 1, 1),
                    new LootItem("smg.thompson", 1, 1),
                    new LootItem("supply.signal", 1, 1),
                    new LootItem("targeting.computer", 1, 1),
                    new LootItem("metal.refined", 150, 150),
                    new LootItem("stones", 7500, 15000),
                    new LootItem("sulfur", 2500, 7500),
                    new LootItem("metal.fragments", 2500, 7500),
                    new LootItem("charcoal", 1000, 5000),
                    new LootItem("gunpowder", 1000, 3500),
                    new LootItem("scrap", 100, 150)
                };
            }
        }

        public class Color1Settings
        {
            [JsonProperty(PropertyName = "Normal")]
            public string Normal { get; set; } = "000000";
            
            public string Get()
            {
                return Normal.StartsWith("#") ? Normal : $"#{Normal}";
            }
        }

        public class Color2Settings
        {
            [JsonProperty(PropertyName = "Normal")]
            public string Normal { get; set; } = "00FF00";

            public string Get()
            {
                return Normal.StartsWith("#") ? Normal : $"#{Normal}";
            }
        }

        public class ManagementMountableSettings
        {
            [JsonProperty(PropertyName = "All Controlled Mounts")]
            public bool ControlledMounts { get; set; }

            [JsonProperty(PropertyName = "All Other Mounts")]
            public bool Other { get; set; }

            [JsonProperty(PropertyName = "Boats")]
            public bool Boats { get; set; }

            [JsonProperty(PropertyName = "Campers")]
            public bool Campers { get; set; } = true;

            [JsonProperty(PropertyName = "Cars (Basic)")]
            public bool BasicCars { get; set; }

            [JsonProperty(PropertyName = "Cars (Modular)")]
            public bool ModularCars { get; set; }

            [JsonProperty(PropertyName = "Chinook")]
            public bool CH47 { get; set; }

            [JsonProperty(PropertyName = "Flying Carpet")]
            public bool FlyingCarpet { get; set; }

            [JsonProperty(PropertyName = "Horses")]
            public bool Horses { get; set; }

            [JsonProperty(PropertyName = "HotAirBalloon")]
            public bool HotAirBalloon { get; set; } = true;

            [JsonProperty(PropertyName = "Jetpacks")]
            public bool Jetpacks { get; set; } = true;

            [JsonProperty(PropertyName = "MiniCopters")]
            public bool MiniCopters { get; set; }

            [JsonProperty(PropertyName = "Pianos")]
            public bool Pianos { get; set; } = true;

            [JsonProperty(PropertyName = "Scrap Transport Helicopters")]
            public bool Scrap { get; set; }

            [JsonProperty(PropertyName = "Snowmobiles")]
            public bool Snowmobile { get; set; }
        }

        public class BuildingOptionsSetupSettings
        {
            [JsonProperty(PropertyName = "Amount Of Entities To Spawn Per Batch")]
            public int SpawnLimit { get; set; } = 1;

            [JsonProperty(PropertyName = "Amount Of Entities To Despawn Per Batch")]
            public int DespawnLimit { get; set; } = 10;

            [JsonProperty(PropertyName = "Height Adjustment Applied To This Paste")]
            public float PasteHeightAdjustment { get; set; }

            [JsonProperty(PropertyName = "Force All Bases To Spawn At Height Level (0 = Water)")]
            public float ForcedHeight { get; set; } = -1f;

            [JsonProperty(PropertyName = "Foundations Immune To Damage When Forced Height Is Applied")]
            public bool FoundationsImmune { get; set; }
        }

        public class ManagementPlayerAmountsSettings
        {
            [JsonProperty(PropertyName = "Maintained Events")]
            public int Maintained { get; set; }

            [JsonProperty(PropertyName = "Manual Events")]
            public int Manual { get; set; }

            [JsonProperty(PropertyName = "Scheduled Events")]
            public int Scheduled { get; set; }

            [JsonProperty(PropertyName = "Bypass For PVP Bases")]
            public bool BypassPVP { get; set; }

            public int Get(RaidableType type)
            {
                switch (type)
                {
                    case RaidableType.Maintained: return Maintained;
                    case RaidableType.Scheduled: return Scheduled;
                    default: return Manual;
                }
            }
        }

        public class ManagementDropSettings
        {
            [JsonProperty(PropertyName = "Auto Turrets")]
            public bool AutoTurret { get; set; }

            [JsonProperty(PropertyName = "Flame Turret")]
            public bool FlameTurret { get; set; }

            [JsonProperty(PropertyName = "Fog Machine")]
            public bool FogMachine { get; set; }

            [JsonProperty(PropertyName = "Gun Trap")]
            public bool GunTrap { get; set; }

            [JsonProperty(PropertyName = "SAM Site")]
            public bool SamSite { get; set; }
        }

        public class ManagementSettingsLocations
        {
            [JsonProperty(PropertyName = "position")]
            public string _position;
            public float radius;
            public ManagementSettingsLocations() { }
            public ManagementSettingsLocations(Vector3 position, float radius)
            {
                this._position = position.ToString();
                this.radius = radius;
            }
            [JsonIgnore]
            public Vector3 position { get { try { return _position.ToVector3(); } catch { Puts("You have configured a blocked spawn position incorrectly: {0}", _position); return Vector3.zero; } } }
        }

        public class ManagementSettings
        {
            [JsonProperty(PropertyName = "Grids To Block Spawns At", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> BlockedGrids { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Block Spawns At Positions", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<ManagementSettingsLocations> BlockedPositions { get; set; } = new List<ManagementSettingsLocations> { new ManagementSettingsLocations(Vector3.zero, 200f) };

            [JsonProperty(PropertyName = "Additional Map Prefabs To Block Spawns At", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public Dictionary<string, float> BlockedPrefabs { get; set; } = new Dictionary<string, float> { ["test_prefab"] = 150f, ["test_prefab_2"] = 125.25f };

            [JsonProperty(PropertyName = "Eject Mounts")]
            public ManagementMountableSettings Mounts { get; set; } = new ManagementMountableSettings();

            [JsonProperty(PropertyName = "Max Amount Of Players Allowed To Enter (0 = infinite, -1 = none)")]
            public ManagementPlayerAmountsSettings Players { get; set; } = new ManagementPlayerAmountsSettings();

            [JsonProperty(PropertyName = "Additional Containers To Include As Boxes", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Inherit { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Difficulty Colors (Border)", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public Color1Settings Colors1 { get; set; } = new Color1Settings();

            [JsonProperty(PropertyName = "Difficulty Colors (Inner)", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public Color2Settings Colors2 { get; set; } = new Color2Settings();

            [JsonProperty(PropertyName = "Entities Allowed To Drop Loot")]
            public ManagementDropSettings DropLoot { get; set; } = new ManagementDropSettings();

            [JsonProperty(PropertyName = "Additional Blocked Colliders", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> AdditionalBlockedColliders { get; set; } = new List<string> { "cube" };

            [JsonProperty(PropertyName = "Allow Teleport")]
            public bool AllowTeleport { get; set; }

            [JsonProperty(PropertyName = "Allow Cupboard Loot To Drop")]
            public bool AllowCupboardLoot { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Players To Build")]
            public bool AllowBuilding { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Players To Use Ladders")]
            public bool AllowLadders { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Players To Upgrade Event Buildings")]
            public bool AllowUpgrade { get; set; }

            [JsonProperty(PropertyName = "Allow Player Bags To Be Lootable At PVP Bases")]
            public bool PlayersLootableInPVP { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Player Bags To Be Lootable At PVE Bases")]
            public bool PlayersLootableInPVE { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Players To Loot Traps")]
            public bool LootableTraps { get; set; }

            [JsonProperty(PropertyName = "Allow Npcs To Target Other Npcs")]
            public bool TargetNpcs { get; set; }

            [JsonProperty(PropertyName = "Allow Raid Bases Inland")]
            public bool AllowInland { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Raid Bases On Beaches")]
            public bool AllowOnBeach { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Raid Bases On Ice Sheets")]
            public bool AllowOnIceSheets { get; set; }

            [JsonProperty(PropertyName = "Allow Raid Bases On Roads")]
            public bool AllowOnRoads { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Raid Bases On Rivers")]
            public bool AllowOnRivers { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Raid Bases On Railroads")]
            public bool AllowOnRailroads { get; set; }

            [JsonProperty(PropertyName = "Allow Raid Bases On Building Topology")]
            public bool AllowOnBuildingTopology { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Raid Bases On Monument Topology")]
            public bool AllowOnMonumentTopology { get; set; }

            [JsonProperty(PropertyName = "Amount Of Spawn Position Checks Per Frame (ADVANCED USERS ONLY)")]
            public int SpawnChecks { get; set; } = 25;

            [JsonProperty(PropertyName = "Allow Vending Machines To Broadcast")]
            public bool AllowBroadcasting { get; set; }

            [JsonProperty(PropertyName = "Backpacks Can Be Opened At PVE Bases")]
            public bool BackpacksOpenPVE { get; set; } = true;

            [JsonProperty(PropertyName = "Backpacks Can Be Opened At PVP Bases")]
            public bool BackpacksOpenPVP { get; set; } = true;

            [JsonProperty(PropertyName = "Backpacks Drop At PVE Bases")]
            public bool BackpacksPVE { get; set; }

            [JsonProperty(PropertyName = "Backpacks Drop At PVP Bases")]
            public bool BackpacksPVP { get; set; }

            [JsonProperty(PropertyName = "Block Npc Kits Plugin")]
            public bool BlockNpcKits { get; set; }

            [JsonProperty(PropertyName = "Block Helicopter Damage To Bases")]
            public bool BlockHelicopterDamage { get; set; }

            [JsonProperty(PropertyName = "Block Mounted Damage To Bases And Players")]
            public bool BlockMounts { get; set; }

            [JsonProperty(PropertyName = "Block Mini Collision Damage")]
            public bool MiniCollision { get; set; }

            [JsonProperty(PropertyName = "Block DoubleJump Plugin")]
            public bool NoDoubleJump { get; set; } = true;

            [JsonProperty(PropertyName = "Block RestoreUponDeath Plugin For PVP Bases")]
            public bool BlockRestorePVP { get; set; }

            [JsonProperty(PropertyName = "Block RestoreUponDeath Plugin For PVE Bases")]
            public bool BlockRestorePVE { get; set; }

            [JsonProperty(PropertyName = "Block LifeSupport Plugin")]
            public bool NoLifeSupport { get; set; } = true;

            [JsonProperty(PropertyName = "Block Rewards During Server Restart")]
            public bool Restart { get; set; }

            [JsonProperty(PropertyName = "Bypass Lock Treasure To First Attacker For PVE Bases")]
            public bool BypassUseOwnersForPVE { get; set; }

            [JsonProperty(PropertyName = "Bypass Lock Treasure To First Attacker For PVP Bases")]
            public bool BypassUseOwnersForPVP { get; set; }

            [JsonProperty(PropertyName = "Despawn Spawned Mounts")]
            public bool DespawnMounts { get; set; } = true;

            [JsonProperty(PropertyName = "Do Not Destroy Player Built Deployables")]
            public bool DoNotDestroyDeployables { get; set; } = true;

            [JsonProperty(PropertyName = "Do Not Destroy Player Built Structures")]
            public bool DoNotDestroyStructures { get; set; } = true;

            [JsonProperty(PropertyName = "Distance To Spawn From Center Of Map")]
            public float Vector3ZeroDistance { get; set; } = 200f;

            [JsonProperty(PropertyName = "Divide Rewards Among All Raiders")]
            public bool DivideRewards { get; set; } = true;

            [JsonProperty(PropertyName = "Draw Corpse Time (Seconds)")]
            public float DrawTime { get; set; } = 300f;

            [JsonProperty(PropertyName = "Destroy Boxes Clipped Too Far Into Terrain")]
            public bool ClippedBoxes { get; set; } = true;

            [JsonProperty(PropertyName = "Destroy Turrets Clipped Too Far Into Terrain")]
            public bool ClippedTurrets { get; set; } = true;

            [JsonProperty(PropertyName = "Eject Sleepers Before Spawning Base")]
            public bool EjectSleepers { get; set; } = true;

            [JsonProperty(PropertyName = "Eject Scavengers When Raid Is Completed")]
            public bool EjectScavengers { get; set; } = true;

            [JsonProperty(PropertyName = "Extra Distance To Spawn From Monuments")]
            public float MonumentDistance { get; set; } = 25f;

            [JsonProperty(PropertyName = "Move Cookables Into Ovens")]
            public bool Cook { get; set; } = true;

            [JsonProperty(PropertyName = "Move Food Into BBQ Or Fridge")]
            public bool Food { get; set; } = true;

            [JsonProperty(PropertyName = "Blacklist For BBQ And Fridge", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public HashSet<string> Foods { get; set; } = new HashSet<string> { "syrup", "pancakes" };

            [JsonProperty(PropertyName = "Move Resources Into Tool Cupboard")]
            public bool Cupboard { get; set; } = true;

            [JsonProperty(PropertyName = "Move Items Into Lockers")]
            public bool Lockers { get; set; } = true;

            [JsonProperty(PropertyName = "Lock Treasure To First Attacker")]
            public bool UseOwners { get; set; } = true;

            [JsonProperty(PropertyName = "Lock Treasure Max Inactive Time (Minutes)")]
            public float LockTime { get; set; } = 20f;

            [JsonProperty(PropertyName = "Lock Players To Raid Base After Entering Zone")]
            public bool LockToRaidOnEnter { get; set; }

            [JsonProperty(PropertyName = "Only Award First Attacker and Allies")]
            public bool OnlyAwardAllies { get; set; }

            [JsonProperty(PropertyName = "Only Award Owner Of Raid")]
            public bool OnlyAwardOwner { get; set; }
            
            [JsonProperty(PropertyName = "Minutes Until Despawn After Looting (min: 1)")]
            public int DespawnMinutes { get; set; } = 15;

            [JsonProperty(PropertyName = "Minutes Until Despawn After Looting Resets When Damaged")]
            public bool DespawnMinutesReset { get; set; }

            [JsonProperty(PropertyName = "Minutes Until Despawn After Inactive (0 = disabled)")]
            public int DespawnMinutesInactive { get; set; } = 45;

            [JsonProperty(PropertyName = "Minutes Until Despawn After Inactive Resets When Damaged")]
            public bool DespawnMinutesInactiveReset { get; set; } = true;

            [JsonProperty(PropertyName = "Mounts Can Take Damage From Players")]
            public bool MountDamageFromPlayers { get; set; }

            [JsonProperty(PropertyName = "Player Cupboard Detection Radius")]
            public float CupboardDetectionRadius { get; set; } = 125f;

            [JsonProperty(PropertyName = "Players With PVP Delay Can Damage Anything Inside Zone")]
            public bool PVPDelayDamageInside { get; set; }

            [JsonProperty(PropertyName = "Players With PVP Delay Can Damage Other Players With PVP Delay Anywhere")]
            public bool PVPDelayAnywhere { get; set; }

            [JsonProperty(PropertyName = "PVP Delay Between Zone Hopping")]
            public float PVPDelay { get; set; } = 10f;

            [JsonProperty(PropertyName = "Prevent Fire From Spreading")]
            public bool PreventFireFromSpreading { get; set; } = true;

            [JsonProperty(PropertyName = "Prevent Players From Hogging Raids")]
            public bool PreventHogging { get; set; } = true;

            [JsonProperty(PropertyName = "Block Clans From Owning More Than One Raid")]
            public bool BlockClans { get; set; }

            [JsonProperty(PropertyName = "Block Friends From Owning More Than One Raid")]
            public bool BlockFriends { get; set; }

            [JsonProperty(PropertyName = "Block Teams From Owning More Than One Raid")]
            public bool BlockTeams { get; set; }

            [JsonProperty(PropertyName = "Prevent Fall Damage When Base Despawns")]
            public bool PreventFallDamage { get; set; }

            [JsonProperty(PropertyName = "Require Cupboard To Be Looted Before Despawning")]
            public bool RequireCupboardLooted { get; set; }

            [JsonProperty(PropertyName = "Destroying The Cupboard Completes The Raid")]
            public bool EndWhenCupboardIsDestroyed { get; set; }

            [JsonProperty(PropertyName = "Require All Bases To Spawn Before Respawning An Existing Base")]
            public bool RequireAllSpawned { get; set; }

            [JsonProperty(PropertyName = "Turn Lights On At Night")]
            public bool Lights { get; set; } = true;

            [JsonProperty(PropertyName = "Turn Lights On Indefinitely")]
            public bool AlwaysLights { get; set; }

            [JsonProperty(PropertyName = "Traps And Turrets Ignore Users Using NOCLIP")]
            public bool IgnoreFlying { get; set; }

            [JsonProperty(PropertyName = "Use Random Codes On Code Locks")]
            public bool RandomCodes { get; set; } = true;

            [JsonProperty(PropertyName = "Wait To Start Despawn Timer When Base Takes Damage From Player")]
            public bool Engaged { get; set; }

            [JsonProperty(PropertyName = "Maximum Water Depth For All Npcs")]
            public float WaterDepth { get; set; } = 3f;

            public bool IsBlocking() => BlockClans || BlockFriends || BlockTeams;
        }

        public class PluginSettingsMapMarkers
        {
            [JsonProperty(PropertyName = "Marker Name")]
            public string MarkerName { get; set; } = "Raidable Base Event";

            [JsonProperty(PropertyName = "Radius")]
            public float Radius { get; set; } = 0.25f;

            [JsonProperty(PropertyName = "Radius (Map Size 3600 Or Less)")]
            public float SubRadius { get; set; } = 0.25f;

            [JsonProperty(PropertyName = "Use Vending Map Marker")]
            public bool UseVendingMarker { get; set; } = true;

            [JsonProperty(PropertyName = "Show Owners Name on Map Marker")]
            public bool ShowOwnersName { get; set; } = true;

            [JsonProperty(PropertyName = "Use Explosion Map Marker")]
            public bool UseExplosionMarker { get; set; }

            [JsonProperty(PropertyName = "Create Markers For Maintained Events")]
            public bool Maintained { get; set; } = true;

            [JsonProperty(PropertyName = "Create Markers For Scheduled Events")]
            public bool Scheduled { get; set; } = true;

            [JsonProperty(PropertyName = "Create Markers For Manual Events")]
            public bool Manual { get; set; } = true;
        }

        public class ExperimentalSettings
        {
            [JsonProperty(PropertyName = "Apply Custom Auto Height To", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> AutoHeight { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Bunker Bases Or Profiles", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Bunker { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Multi Foundation Bases Or Profiles", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> MultiFoundation { get; set; } = new List<string>();

            public enum Type { AutoHeight, Bunker, MultiFoundation };

            public bool Contains(Type type, RandomBase rb)
            {
                switch (type)
                {
                    case Type.AutoHeight: return AutoHeight.Contains("*") || AutoHeight.Contains(rb.BaseName) || AutoHeight.Contains(rb.Profile.ProfileName);
                    case Type.Bunker: return Bunker.Contains("*") || Bunker.Contains(rb.BaseName) || Bunker.Contains(rb.Profile.ProfileName);
                    case Type.MultiFoundation: return MultiFoundation.Contains("*") || MultiFoundation.Contains(rb.BaseName) || MultiFoundation.Contains(rb.Profile.ProfileName);
                    default: return false;
                }
            }
        }

        public class PluginSettings
        {
            [JsonProperty(PropertyName = "Experimental [* = everything]")]
            public ExperimentalSettings Experimental { get; set; } = new ExperimentalSettings();

            [JsonProperty(PropertyName = "Raid Management")]
            public ManagementSettings Management { get; set; } = new ManagementSettings();

            [JsonProperty(PropertyName = "Map Markers")]
            public PluginSettingsMapMarkers Markers { get; set; } = new PluginSettingsMapMarkers();

            [JsonProperty(PropertyName = "Maintained Events")]
            public RaidableBaseSettingsMaintained Maintained { get; set; } = new RaidableBaseSettingsMaintained();

            [JsonProperty(PropertyName = "Manual Events")]
            public RaidableBaseSettingsManual Manual { get; set; } = new RaidableBaseSettingsManual();

            [JsonProperty(PropertyName = "Scheduled Events")]
            public RaidableBaseSettingsScheduled Schedule { get; set; } = new RaidableBaseSettingsScheduled();

            [JsonProperty(PropertyName = "Allowed Zone Manager Zones", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Inclusions { get; set; } = new List<string> { "pvp", "99999999" };

            [JsonProperty(PropertyName = "Use Grid Locations In Allowed Zone Manager Zones Only")]
            public bool UseZoneManagerOnly { get; set; }

            [JsonProperty(PropertyName = "Extended Distance To Spawn Away From Zone Manager Zones")]
            public float ZoneDistance { get; set; } = 25f;

            [JsonProperty(PropertyName = "Blacklisted Commands", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> BlacklistedCommands { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Automatically Teleport Admins To Their Map Marker Positions")]
            public bool TeleportMarker { get; set; } = true;

            [JsonProperty(PropertyName = "Automatically Destroy Markers That Admins Teleport To")]
            public bool DestroyMarker { get; set; }

            [JsonProperty(PropertyName = "Block Archery Plugin At Events")]
            public bool NoArchery { get; set; }

            [JsonProperty(PropertyName = "Block Wizardry Plugin At Events")]
            public bool NoWizardry { get; set; }

            [JsonProperty(PropertyName = "Chat Steam64ID")]
            public ulong ChatID { get; set; }

            [JsonProperty(PropertyName = "Expansion Mode (Dangerous Treasures)")]
            public bool ExpansionMode { get; set; }

            [JsonProperty(PropertyName = "Remove Admins From Raiders List")]
            public bool RemoveAdminRaiders { get; set; }

            [JsonProperty(PropertyName = "Show X Z Coordinates")]
            public bool ShowXZ { get; set; }

            [JsonProperty(PropertyName = "Event Command")]
            public string EventCommand { get; set; } = "rbe";

            [JsonProperty(PropertyName = "Hunter Command")]
            public string HunterCommand { get; set; } = "rb";

            [JsonProperty(PropertyName = "Server Console Command")]
            public string ConsoleCommand { get; set; } = "rbevent";
        }

        public class EventMessageRewardSettings
        {
            [JsonProperty(PropertyName = "Flying")]
            public bool Flying { get; set; }

            [JsonProperty(PropertyName = "Vanished")]
            public bool Vanished { get; set; }

            [JsonProperty(PropertyName = "Inactive")]
            public bool Inactive { get; set; } = true;

            [JsonProperty(PropertyName = "Not An Ally")]
            public bool NotAlly { get; set; } = true;

            [JsonProperty(PropertyName = "Not The Owner")]
            public bool NotOwner { get; set; } = true;

            [JsonProperty(PropertyName = "Not A Participant")]
            public bool NotParticipant { get; set; } = true;

            [JsonProperty(PropertyName = "Remove Admins From Raiders List")]
            public bool RemoveAdmin { get; set; }
        }

        public class EventMessageSettings
        {
            [JsonProperty(PropertyName = "Ineligible For Rewards")]
            public EventMessageRewardSettings Rewards { get; set; } = new EventMessageRewardSettings();

            [JsonProperty(PropertyName = "Announce Raid Unlocked")]
            public bool AnnounceRaidUnlock { get; set; }

            [JsonProperty(PropertyName = "Announce Thief Message")]
            public bool AnnounceThief { get; set; } = true;

            [JsonProperty(PropertyName = "Announce PVE/PVP Enter/Exit Messages")]
            public bool AnnounceEnterExit { get; set; } = true;

            [JsonProperty(PropertyName = "Show Destroy Warning")]
            public bool ShowWarning { get; set; } = true;

            [JsonProperty(PropertyName = "Show Opened Message For PVE Bases")]
            public bool OpenedPVE { get; set; } = true;

            [JsonProperty(PropertyName = "Show Opened Message For PVP Bases")]
            public bool OpenedPVP { get; set; } = true;

            [JsonProperty(PropertyName = "Show Prefix")]
            public bool Prefix { get; set; } = true;

            [JsonProperty(PropertyName = "Notify Plugin - Type (-1 = disabled)")]
            public int NotifyType { get; set; } = -1;

            [JsonProperty(PropertyName = "Notification Interval")]
            public float Interval { get; set; } = 1f;

            [JsonProperty(PropertyName = "Send Messages To Player")]
            public bool Message { get; set; } = true;

            [JsonProperty(PropertyName = "Save Thieves To Log File")]
            public bool LogThieves { get; set; }
        }

        public class GUIAnnouncementSettings
        {
            [JsonProperty(PropertyName = "Enabled")]
            public bool Enabled { get; set; }

            [JsonProperty(PropertyName = "Banner Tint Color")]
            public string TintColor { get; set; } = "Grey";

            [JsonProperty(PropertyName = "Maximum Distance")]
            public float Distance { get; set; } = 300f;

            [JsonProperty(PropertyName = "Text Color")]
            public string TextColor { get; set; } = "White";
        }

        public class NpcKitSettings
        {
            [JsonProperty(PropertyName = "Helm", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Helm { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Torso", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Torso { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Pants", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Pants { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Gloves", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Gloves { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Boots", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Boots { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Shirt", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Shirt { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Kilts", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Kilts { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Weapon", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Weapon { get; set; } = new List<string>();

            public NpcKitSettings(bool isMurderer)
            {
                if (isMurderer)
                {
                    Helm.Add("metal.facemask");
                    Torso.Add("metal.plate.torso");
                    Pants.Add("pants");
                    Gloves.Add("tactical.gloves");
                    Boots.Add("boots.frog");
                    Shirt.Add("tshirt");
                    Weapon.Add("machete");
                }
                else
                {
                    Torso.Add("hazmatsuit_scientist_peacekeeper");
                    Weapon.Add("rifle.ak");
                }
            }
        }

        public class NpcMultiplierSettings
        {
            [JsonProperty(PropertyName = "Gun Damage Multiplier")]
            public float ProjectileDamageMultiplier { get; set; } = 1f;

            [JsonProperty(PropertyName = "Melee Damage Multiplier")]
            public float MeleeDamageMultiplier { get; set; } = 1f;
        }

        public class NpcSettingsAccuracyDifficulty
        {
            [JsonProperty(PropertyName = "AK47")]
            public double AK47 { get; set; }

            [JsonProperty(PropertyName = "AK47 ICE")]
            public double AK47ICE { get; set; }

            [JsonProperty(PropertyName = "Bolt Rifle")]
            public double BOLT_RIFLE { get; set; }

            [JsonProperty(PropertyName = "Compound Bow")]
            public double COMPOUND_BOW { get; set; }

            [JsonProperty(PropertyName = "Crossbow")]
            public double CROSSBOW { get; set; }

            [JsonProperty(PropertyName = "Double Barrel Shotgun")]
            public double DOUBLE_SHOTGUN { get; set; }

            [JsonProperty(PropertyName = "Eoka")]
            public double EOKA { get; set; }

            [JsonProperty(PropertyName = "Glock")]
            public double GLOCK { get; set; }

            [JsonProperty(PropertyName = "HMLMG")]
            public double HMLMG { get; set; }

            [JsonProperty(PropertyName = "L96")]
            public double L96 { get; set; }

            [JsonProperty(PropertyName = "LR300")]
            public double LR300 { get; set; }

            [JsonProperty(PropertyName = "M249")]
            public double M249 { get; set; }

            [JsonProperty(PropertyName = "M39")]
            public double M39 { get; set; }

            [JsonProperty(PropertyName = "M92")]
            public double M92 { get; set; }

            [JsonProperty(PropertyName = "MP5")]
            public double MP5 { get; set; }

            [JsonProperty(PropertyName = "Nailgun")]
            public double NAILGUN { get; set; }

            [JsonProperty(PropertyName = "Pump Shotgun")]
            public double PUMP_SHOTGUN { get; set; }

            [JsonProperty(PropertyName = "Python")]
            public double PYTHON { get; set; }

            [JsonProperty(PropertyName = "Revolver")]
            public double REVOLVER { get; set; }

            [JsonProperty(PropertyName = "Semi Auto Pistol")]
            public double SEMI_AUTO_PISTOL { get; set; }

            [JsonProperty(PropertyName = "Semi Auto Rifle")]
            public double SEMI_AUTO_RIFLE { get; set; }

            [JsonProperty(PropertyName = "Spas12")]
            public double SPAS12 { get; set; }

            [JsonProperty(PropertyName = "Speargun")]
            public double SPEARGUN { get; set; }

            [JsonProperty(PropertyName = "SMG")]
            public double SMG { get; set; }

            [JsonProperty(PropertyName = "Snowball Gun")]
            public double SNOWBALL_GUN { get; set; }

            [JsonProperty(PropertyName = "Thompson")]
            public double THOMPSON { get; set; }

            [JsonProperty(PropertyName = "Waterpipe Shotgun")]
            public double WATERPIPE_SHOTGUN { get; set; }

            public NpcSettingsAccuracyDifficulty(double accuracy)
            {
                AK47 = AK47ICE = BOLT_RIFLE = COMPOUND_BOW = CROSSBOW = DOUBLE_SHOTGUN = EOKA = GLOCK = HMLMG = L96 = LR300 = M249 = M39 = M92 = MP5 = NAILGUN = PUMP_SHOTGUN = PYTHON = REVOLVER = SEMI_AUTO_PISTOL = SEMI_AUTO_RIFLE = SPAS12 = SPEARGUN = SMG = SNOWBALL_GUN = THOMPSON = WATERPIPE_SHOTGUN = accuracy;
            }

            public double Get(HumanoidBrain brain)
            {
                switch (brain.AttackEntity?.ShortPrefabName)
                {
                    case "ak47u.entity": return AK47;
                    case "ak47u_ice.entity": return AK47ICE;
                    case "bolt_rifle.entity": return BOLT_RIFLE;
                    case "compound_bow.entity": return COMPOUND_BOW;
                    case "crossbow.entity": return CROSSBOW;
                    case "double_shotgun.entity": return DOUBLE_SHOTGUN;
                    case "glock.entity": return GLOCK;
                    case "hmlmg.entity": return HMLMG;
                    case "l96.entity": return L96;
                    case "lr300.entity": return LR300;
                    case "m249.entity": return M249;
                    case "m39.entity": return M39;
                    case "m92.entity": return M92;
                    case "mp5.entity": return MP5;
                    case "nailgun.entity": return NAILGUN;
                    case "pistol_eoka.entity": return EOKA;
                    case "pistol_revolver.entity": return REVOLVER;
                    case "pistol_semiauto.entity": return SEMI_AUTO_PISTOL;
                    case "python.entity": return PYTHON;
                    case "semi_auto_rifle.entity": return SEMI_AUTO_RIFLE;
                    case "shotgun_pump.entity": return PUMP_SHOTGUN;
                    case "shotgun_waterpipe.entity": return WATERPIPE_SHOTGUN;
                    case "spas12.entity": return SPAS12;
                    case "speargun.entity": return SPEARGUN;
                    case "smg.entity": return SMG;
                    case "snowballgun.entity": return SNOWBALL_GUN;
                    case "thompson.entity": default: return THOMPSON;
                }
            }
        }

        public class NpcSettings
        {
            public NpcSettings() { }

            public NpcSettings(double accuracy)
            {
                Accuracy = new NpcSettingsAccuracyDifficulty(accuracy);
            }

            [JsonProperty(PropertyName = "Weapon Accuracy (0 - 100)")]
            public NpcSettingsAccuracyDifficulty Accuracy { get; set; }

            [JsonProperty(PropertyName = "Damage Multipliers")]
            public NpcMultiplierSettings Multipliers { get; set; } = new NpcMultiplierSettings();

            [JsonProperty(PropertyName = "Murderer (Items)")]
            public NpcKitSettings MurdererItems { get; set; } = new NpcKitSettings(true);

            [JsonProperty(PropertyName = "Scientist (Items)")]
            public NpcKitSettings ScientistItems { get; set; } = new NpcKitSettings(false);

            [JsonProperty(PropertyName = "Murderer Kits", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> MurdererKits { get; set; } = new List<string> { "murderer_kit_1", "murderer_kit_2" };

            [JsonProperty(PropertyName = "Scientist Kits", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> ScientistKits { get; set; } = new List<string> { "scientist_kit_1", "scientist_kit_2" };

            [JsonProperty(PropertyName = "Random Names", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> RandomNames { get; set; } = new List<string>();

            [JsonProperty(PropertyName = "Enabled")]
            public bool Enabled { get; set; } = true;

            [JsonProperty(PropertyName = "Amount Of Murderers To Spawn")]
            public int SpawnAmountMurderers { get; set; } = -9;

            [JsonProperty(PropertyName = "Minimum Amount Of Murderers To Spawn")]
            public int SpawnMinAmountMurderers { get; set; } = -9;

            [JsonProperty(PropertyName = "Spawn Random Amount Of Murderers")]
            public bool SpawnRandomAmountMurderers { get; set; }

            [JsonProperty(PropertyName = "Amount Of Scientists To Spawn")]
            public int SpawnAmountScientists { get; set; } = -9;

            [JsonProperty(PropertyName = "Minimum Amount Of Scientists To Spawn")]
            public int SpawnMinAmountScientists { get; set; } = -9;

            [JsonProperty(PropertyName = "Spawn Random Amount Of Scientists")]
            public bool SpawnRandomAmountScientists { get; set; }

            [JsonProperty(PropertyName = "Allow Npcs To Leave Dome When Attacking")]
            public bool CanLeave { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Npcs To Shoot Players Outside Of The Dome")]
            public bool CanShoot { get; set; } = true;

            [JsonProperty(PropertyName = "Aggression Range")]
            public float AggressionRange { get; set; } = 70f;

            [JsonProperty(PropertyName = "Block Damage Outside To Npcs When Not Allowed To Leave Dome")]
            public bool BlockOutsideDamageOnLeave { get; set; } = true;

            [JsonProperty(PropertyName = "Block Damage Outside Of The Dome To Npcs Inside")]
            public bool BlockOutsideDamageToNpcsInside { get; set; }

            [JsonProperty(PropertyName = "Despawn Inventory On Death")]
            public bool DespawnInventory { get; set; } = true;

            [JsonProperty(PropertyName = "Health For Murderers (100 min, 5000 max)")]
            public float MurdererHealth { get; set; } = 150f;

            [JsonProperty(PropertyName = "Health For Scientists (100 min, 5000 max)")]
            public float ScientistHealth { get; set; } = 150f;

            [JsonProperty(PropertyName = "Kill Underwater Npcs")]
            public bool KillUnderwater { get; set; } = true;

            [JsonProperty(PropertyName = "Player Traps And Turrets Ignore Npcs")]
            public bool IgnorePlayerTrapsTurrets { get; set; }

            [JsonProperty(PropertyName = "Event Traps And Turrets Ignore Npcs")]
            public bool IgnoreTrapsTurrets { get; set; } = true;

            [JsonProperty(PropertyName = "Use Dangerous Treasures NPCs")]
            public bool UseExpansionNpcs { get; set; }
        }

        public class PasteOption
        {
            [JsonProperty(PropertyName = "Option")]
            public string Key { get; set; }

            [JsonProperty(PropertyName = "Value")]
            public string Value { get; set; }
        }

        public class BuildingLevels
        {
            [JsonProperty(PropertyName = "Level 2 - Final Death")]
            public bool Level2 { get; set; }
        }

        public class DoorTypes
        {
            [JsonProperty(PropertyName = "Wooden")]
            public bool Wooden { get; set; }

            [JsonProperty(PropertyName = "Metal")]
            public bool Metal { get; set; }

            [JsonProperty(PropertyName = "HQM")]
            public bool HQM { get; set; }

            [JsonProperty(PropertyName = "Include Garage Doors")]
            public bool GarageDoor { get; set; }

            public bool Any() => Wooden || Metal || HQM;
        }

        public class BuildingGradeLevels
        {
            [JsonProperty(PropertyName = "Wooden")]
            public bool Wooden { get; set; }

            [JsonProperty(PropertyName = "Stone")]
            public bool Stone { get; set; }

            [JsonProperty(PropertyName = "Metal")]
            public bool Metal { get; set; }

            [JsonProperty(PropertyName = "HQM")]
            public bool HQM { get; set; }

            public bool Any() => Wooden || Stone || Metal || HQM;
        }

        public class BuildingOptionsAutoTurrets
        {
            [JsonProperty(PropertyName = "Aim Cone")]
            public float AimCone { get; set; } = 5f;

            [JsonProperty(PropertyName = "Wait To Power On Until Event Starts")]
            public bool InitiateOnSpawn { get; set; }

            [JsonProperty(PropertyName = "Minimum Damage Modifier")]
            public float Min { get; set; } = 1f;

            [JsonProperty(PropertyName = "Maximum Damage Modifier")]
            public float Max { get; set; } = 1f;

            [JsonProperty(PropertyName = "Start Health")]
            public float Health { get; set; } = 1000f;

            [JsonProperty(PropertyName = "Sight Range")]
            public float SightRange { get; set; } = 30f;

            [JsonProperty(PropertyName = "Double Sight Range When Shot")]
            public bool AutoAdjust { get; set; }

            [JsonProperty(PropertyName = "Set Hostile (False = Do Not Set Any Mode)")]
            public bool Hostile { get; set; } = true;

            [JsonProperty(PropertyName = "Requires Power Source")]
            public bool RequiresPower { get; set; }

            [JsonProperty(PropertyName = "Remove Equipped Weapon")]
            public bool RemoveWeapon { get; set; }

            [JsonProperty(PropertyName = "Random Weapons To Equip When Unequipped", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Shortnames { get; set; } = new List<string> { "rifle.ak" };
        }

        public class BuildingOptionsProtectionRadius
        {
            [JsonProperty(PropertyName = "Maintained Events")]
            public float Maintained { get; set; }

            [JsonProperty(PropertyName = "Manual Events")]
            public float Manual { get; set; }

            [JsonProperty(PropertyName = "Scheduled Events")]
            public float Scheduled { get; set; }

            [JsonProperty(PropertyName = "Obstruction Distance Check")]
            public float Obstruction { get; set; } = -1f;

            public void Set(float value)
            {
                Maintained = value;
                Manual = value;
                Scheduled = value;
            }

            public float Get(RaidableType type)
            {
                switch (type)
                {
                    case RaidableType.Maintained: return Maintained;
                    case RaidableType.Scheduled: return Scheduled;
                    case RaidableType.Manual: return Manual;
                    default: return Max();
                }
            }

            public float Max() => Mathf.Max(Maintained, Manual, Scheduled);

            public float Min() => Mathf.Min(Maintained, Manual, Scheduled);
        }

        public class BuildingWaterOptions
        {
            [JsonProperty(PropertyName = "Allow Bases To Float Above Water")]
            public bool AllowSubmerged { get; set; }

            [JsonProperty(PropertyName = "Prevent Bases From Floating Above Water By Also Checking Surrounding Area")]
            public bool SubmergedAreaCheck { get; set; }

            [JsonProperty(PropertyName = "Maximum Water Depth Level Used For Float Above Water Option")]
            public float WaterDepth { get; set; } = 1f;
        }

        public class BuildingOptions
        {
            public BuildingOptions() { }

            public BuildingOptions(params string[] bases)
            {
                PasteOptions = DefaultPasteOptions;
                AdditionalBases = new Dictionary<string, List<PasteOption>>();

                if (bases?.Length > 0)
                {
                    foreach (string value in bases)
                    {
                        AdditionalBases[value] = DefaultPasteOptions;
                    }
                }
            }

            [JsonProperty(PropertyName = "Protection Radius", NullValueHandling = NullValueHandling.Ignore)]
            public float? ProtectionRadiusObsolete { get; set; } = 50f;

            [JsonProperty(PropertyName = "Advanced Protection Radius")]
            public BuildingOptionsProtectionRadius ProtectionRadii { get; set; } = new BuildingOptionsProtectionRadius();

            [JsonProperty(PropertyName = "Advanced Setup Settings")]
            public BuildingOptionsSetupSettings Setup { get; set; } = new BuildingOptionsSetupSettings();

            [JsonProperty(PropertyName = "Elevators")]
            public BuildingOptionsElevators Elevators { get; set; } = new BuildingOptionsElevators();

            [JsonProperty(PropertyName = "Entities Not Allowed To Be Picked Up", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> BlacklistedPickupItems { get; set; } = new List<string> { "generator.small", "generator.static", "autoturret_deployed" };

            [JsonProperty(PropertyName = "Additional Bases For This Difficulty", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public Dictionary<string, List<PasteOption>> AdditionalBases { get; set; } = new Dictionary<string, List<PasteOption>>();

            [JsonProperty(PropertyName = "Paste Options", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<PasteOption> PasteOptions { get; set; } = new List<PasteOption>();

            [JsonProperty(PropertyName = "Arena Walls")]
            public RaidableBaseWallOptions ArenaWalls { get; set; } = new RaidableBaseWallOptions();

            [JsonProperty(PropertyName = "NPC Levels")]
            public BuildingLevels Levels { get; set; } = new BuildingLevels();

            [JsonProperty(PropertyName = "NPCs")]
            public NpcSettings NPC { get; set; } = new NpcSettings();

            [JsonProperty(PropertyName = "Rewards")]
            public RewardSettings Rewards { get; set; } = new RewardSettings();

            [JsonProperty(PropertyName = "Change Building Material Tier To")]
            public BuildingGradeLevels Blocks { get; set; } = new BuildingGradeLevels();

            [JsonProperty(PropertyName = "Change Door Type To")]
            public DoorTypes Doors { get; set; } = new DoorTypes();

            [JsonProperty(PropertyName = "Auto Turrets")]
            public BuildingOptionsAutoTurrets AutoTurret { get; set; } = new BuildingOptionsAutoTurrets();

            [JsonProperty(PropertyName = "Player Building Restrictions")]
            public BuildingGradeLevels BuildingRestrictions { get; set; } = new BuildingGradeLevels();

            [JsonProperty(PropertyName = "Water Settings")]
            public BuildingWaterOptions Water { get; set; } = new BuildingWaterOptions();

            [JsonProperty(PropertyName = "Profile Enabled")]
            public bool Enabled { get; set; } = true;

            [JsonProperty(PropertyName = "Maximum Land Level")]
            public float LandLevel { get; set; } = 2.5f;

            [JsonProperty(PropertyName = "Allow Players To Use MLRS")]
            public bool MLRS { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Third-Party Npc Explosive Damage To Bases")]
            public bool RaidingNpcs { get; set; }

            [JsonProperty(PropertyName = "Add Code Lock To Unlocked Or KeyLocked Doors")]
            public bool DoorLock { get; set; } = true;

            [JsonProperty(PropertyName = "Add Key Lock To Unlocked Or CodeLocked Doors")]
            public bool KeyLock { get; set; }

            [JsonProperty(PropertyName = "Add Code Lock To Tool Cupboards")]
            public bool LockPrivilege { get; set; }

            [JsonProperty(PropertyName = "Add Code Lock To Boxes")]
            public bool LockBoxes { get; set; }

            [JsonProperty(PropertyName = "Add Code Lock To Lockers")]
            public bool LockLockers { get; set; } = true;

            [JsonProperty(PropertyName = "Close Open Doors With No Door Controller Installed")]
            public bool CloseOpenDoors { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Duplicate Items")]
            public bool AllowDuplicates { get; set; }

            [JsonProperty(PropertyName = "Allow Players To Pickup Deployables")]
            public bool AllowPickup { get; set; }

            [JsonProperty(PropertyName = "Allow Players To Deploy A Cupboard")]
            public bool AllowBuildingPriviledges { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Players To Deploy Barricades")]
            public bool Barricades { get; set; } = true;

            [JsonProperty(PropertyName = "Allow PVP")]
            public bool AllowPVP { get; set; } = true;

            [JsonProperty(PropertyName = "Allow Friendly Fire (Teams)")]
            public bool AllowFriendlyFire { get; set; } = true;

            [JsonProperty(PropertyName = "Minimum Amount Of Items To Spawn (0 = Use Max Value)")]
            public int MinTreasure { get; set; }

            [JsonProperty(PropertyName = "Amount Of Items To Spawn")]
            public int MaxTreasure { get; set; } = 30;

            [JsonProperty(PropertyName = "Flame Turret Health")]
            public float FlameTurretHealth { get; set; } = 300f;

            [JsonProperty(PropertyName = "Block Plugins Which Prevent Item Durability Loss")]
            public bool EnforceDurability { get; set; }

            [JsonProperty(PropertyName = "Block Damage Outside Of The Dome To Players Inside")]
            public bool BlockOutsideDamageToPlayersInside { get; set; }

            [JsonProperty(PropertyName = "Block Damage Outside Of The Dome To Bases Inside")]
            public bool BlockOutsideDamageToBaseInside { get; set; }

            [JsonProperty(PropertyName = "Block Damage Inside From Npcs To Players Outside")]
            public bool BlockNpcDamageToPlayersOutside { get; set; }

            [JsonProperty(PropertyName = "Building Blocks Are Immune To Damage")]
            public bool BlocksImmune { get; set; }

            [JsonProperty(PropertyName = "Building Blocks Are Immune To Damage (Twig Only)")]
            public bool TwigImmune { get; set; }

            [JsonProperty(PropertyName = "Boxes Are Invulnerable")]
            public bool Invulnerable { get; set; }

            [JsonProperty(PropertyName = "Boxes Are Invulnerable Until Cupboard Is Destroyed")]
            public bool InvulnerableUntilCupboardIsDestroyed { get; set; }

            [JsonProperty(PropertyName = "Spawn Silently (No Notifcation, No Dome, No Map Marker)")]
            public bool Silent { get; set; }

            [JsonProperty(PropertyName = "Despawn Dropped Loot Bags From Raid Boxes When Base Despawns")]
            public bool DespawnGreyBags { get; set; }

            [JsonProperty(PropertyName = "Divide Loot Into All Containers")]
            public bool DivideLoot { get; set; } = true;

            [JsonProperty(PropertyName = "Drop Tool Cupboard Loot After Raid Is Completed")]
            public bool DropPrivilegeLoot { get; set; }

            [JsonProperty(PropertyName = "Drop Container Loot X Seconds After It Is Looted")]
            public float DropTimeAfterLooting { get; set; }

            [JsonProperty(PropertyName = "Drop Container Loot Applies Only To Boxes And Cupboards")]
            public bool DropOnlyBoxesAndPrivileges { get; set; } = true;

            [JsonProperty(PropertyName = "Create Dome Around Event Using Spheres (0 = disabled, recommended = 5)")]
            public int SphereAmount { get; set; } = 5;

            [JsonProperty(PropertyName = "Empty All Containers Before Spawning Loot")]
            public bool EmptyAll { get; set; } = true;

            [JsonProperty(PropertyName = "Empty All Containers (Exclusions)", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> EmptyExemptions { get; set; } = new List<string> { "xmas_tree.deployed", "xmas_tree_a.deployed" };

            [JsonProperty(PropertyName = "Eject Corpses From Enemy Raids (Advanced Users Only)")]
            public bool EjectBackpacks { get; set; } = true;

            [JsonProperty(PropertyName = "Eject Corpses From PVE Instantly (Advanced Users Only)")]
            public bool EjectBackpacksPVE { get; set; }

            [JsonProperty(PropertyName = "Eject Enemies From Locked PVE Raids")]
            public bool EjectLockedPVE { get; set; } = true;

            [JsonProperty(PropertyName = "Eject Enemies From Locked PVP Raids")]
            public bool EjectLockedPVP { get; set; }

            [JsonProperty(PropertyName = "Explosion Damage Modifier (0-999)")]
            public float ExplosionModifier { get; set; } = 100f;

            [JsonProperty(PropertyName = "Force All Boxes To Have Same Skin")]
            public bool SetSkins { get; set; } = true;

            [JsonProperty(PropertyName = "Ignore Containers That Spawn With Loot Already")]
            public bool IgnoreContainedLoot { get; set; }

            [JsonProperty(PropertyName = "Loot Amount Multiplier")]
            public float Multiplier { get; set; } = 1f;

            [JsonProperty(PropertyName = "Maximum Respawn Npc X Seconds After Death")]
            public float RespawnRateMax { get; set; }

            [JsonProperty(PropertyName = "Minimum Respawn Npc X Seconds After Death")]
            public float RespawnRateMin { get; set; }

            [JsonProperty(PropertyName = "No Item Input For Boxes And TC")]
            public bool NoItemInput { get; set; } = true;

            [JsonProperty(PropertyName = "Penalize Players On Death In PVE (ZLevels)")]
            public bool PenalizePVE { get; set; } = true;

            [JsonProperty(PropertyName = "Penalize Players On Death In PVP (ZLevels)")]
            public bool PenalizePVP { get; set; } = true;

            [JsonProperty(PropertyName = "Require Cupboard Access To Loot")]
            public bool RequiresCupboardAccess { get; set; }

            [JsonProperty(PropertyName = "Require Cupboard Access To Place Ladders")]
            public bool RequiresCupboardAccessLadders { get; set; }

            [JsonProperty(PropertyName = "Skip Treasure Loot And Use Loot In Base Only")]
            public bool SkipTreasureLoot { get; set; }

            [JsonProperty(PropertyName = "Use Buoyant Boxex For Dropped Privilege Loot")]
            public bool BuoyantPrivilege { get; set; }

            [JsonProperty(PropertyName = "Use Buoyant Boxex For Dropped Box Loot")]
            public bool BuoyantBox { get; set; }

            [JsonProperty(PropertyName = "Remove Locks When Event Is Completed")]
            public bool UnlockEverything { get; set; }

            [JsonProperty(PropertyName = "Always Spawn Base Loot Table")]
            public bool AlwaysSpawn { get; set; }

            //[JsonProperty(PropertyName = "Eco Raiding", NullValueHandling = NullValueHandling.Ignore)]
            //public BuildingOptionsEco Eco { get; set; } = null;

            public static BuildingOptions Clone(BuildingOptions options)
            {
                return options.MemberwiseClone() as BuildingOptions;
            }

            public float ProtectionRadius(RaidableType type)
            {
                float radius = ProtectionRadii.Get(type);

                return radius < CELL_SIZE ? 50f : radius;
            }
        }

        public class BuildingOptionsEco
        {
            [JsonProperty(PropertyName = "Allow Eco Raiding Only")]
            public bool Enabled { get; set; }

            [JsonProperty(PropertyName = "Allow Flame Throwers")]
            public bool FlameThrowers { get; set; }
        }

        public class RaidableBaseSettingsEventTypeBase
        {
            [JsonProperty(PropertyName = "Convert PVE To PVP")]
            public bool ConvertPVE { get; set; }

            [JsonProperty(PropertyName = "Convert PVP To PVE")]
            public bool ConvertPVP { get; set; }

            [JsonProperty(PropertyName = "Ignore Safe Checks")]
            public bool Ignore { get; set; }

            [JsonProperty(PropertyName = "Ignore Safe Checks In X Radius Only")]
            public float SafeRadius { get; set; }

            [JsonProperty(PropertyName = "Ignore Player Entities At Custom Spawn Locations")]
            public bool Skip { get; set; }

            [JsonProperty(PropertyName = "Spawn Bases X Distance Apart")]
            public float Distance { get; set; } = 100f;

            [JsonProperty(PropertyName = "Spawns Database File (Optional)")]
            public string SpawnsFile { get; set; } = "none";
        }

        public class RaidableBaseSettingsEventTypeBaseExtended : RaidableBaseSettingsEventTypeBase
        {
            [JsonProperty(PropertyName = "Chance To Randomly Spawn PVP Bases (0 = Ignore Setting)")]
            public decimal Chance { get; set; }

            [JsonProperty(PropertyName = "Include PVE Bases")]
            public bool IncludePVE { get; set; } = true;

            [JsonProperty(PropertyName = "Include PVP Bases")]
            public bool IncludePVP { get; set; } = true;

            [JsonProperty(PropertyName = "Minimum Required Players Online")]
            public int PlayerLimit { get; set; } = 1;

            [JsonProperty(PropertyName = "Maximum Limit Of Players Online")]
            public int PlayerLimitMax { get; set; } = 300;

            [JsonProperty(PropertyName = "Time To Wait Between Spawns")]
            public float Time { get; set; } = 15f;
        }

        public class RaidableBaseSettingsScheduled : RaidableBaseSettingsEventTypeBaseExtended
        {
            [JsonProperty(PropertyName = "Enabled")]
            public bool Enabled { get; set; }

            [JsonProperty(PropertyName = "Every Min Seconds")]
            public double IntervalMin { get; set; } = 3600f;

            [JsonProperty(PropertyName = "Every Max Seconds")]
            public double IntervalMax { get; set; } = 7200f;

            [JsonProperty(PropertyName = "Max Scheduled Events")]
            public int Max { get; set; } = 1;

            [JsonProperty(PropertyName = "Max To Spawn At Once (0 = Use Max Scheduled Events Amount)")]
            public int MaxOnce { get; set; }
        }

        public class RaidableBaseSettingsMaintained : RaidableBaseSettingsEventTypeBaseExtended
        {
            [JsonProperty(PropertyName = "Always Maintain Max Events")]
            public bool Enabled { get; set; }

            [JsonProperty(PropertyName = "Max Maintained Events")]
            public int Max { get; set; } = 1;
        }

        public class RaidableBaseSettingsManual
        {
            [JsonProperty(PropertyName = "Convert PVE To PVP")]
            public bool ConvertPVE { get; set; }

            [JsonProperty(PropertyName = "Convert PVP To PVE")]
            public bool ConvertPVP { get; set; }

            [JsonProperty(PropertyName = "Max Manual Events")]
            public int Max { get; set; } = 1;

            [JsonProperty(PropertyName = "Spawns Database File (Optional)")]
            public string SpawnsFile { get; set; } = "none";
        }

        public class RaidableBaseWallOptions
        {
            [JsonProperty(PropertyName = "Enabled")]
            public bool Enabled { get; set; } = true;

            [JsonProperty(PropertyName = "Stacks")]
            public int Stacks { get; set; } = 1;

            [JsonProperty(PropertyName = "Ignore Stack Limit When Clipping Terrain")]
            public bool IgnoreWhenClippingTerrain { get; set; } = true;

            [JsonProperty(PropertyName = "Use Stone Walls")]
            public bool Stone { get; set; } = true;

            [JsonProperty(PropertyName = "Use Iced Walls")]
            public bool Ice { get; set; }

            [JsonProperty(PropertyName = "Use Least Amount Of Walls")]
            public bool LeastAmount { get; set; } = true;

            [JsonProperty(PropertyName = "Use UFO Walls")]
            public bool UseUFOWalls { get; set; }

            [JsonProperty(PropertyName = "Radius")]
            public float Radius { get; set; } = 25f;
        }

        public class RankedLadderSettings
        {
            [JsonProperty(PropertyName = "Award Top X Players On Wipe")]
            public int Amount { get; set; } = 3;

            [JsonProperty(PropertyName = "Enabled")]
            public bool Enabled { get; set; } = true;

            [JsonProperty(PropertyName = "Show Top X Ladder")]
            public int Top { get; set; } = 10;
        }

        public class RewardSettings
        {
            [JsonProperty(PropertyName = "Economics Money")]
            public double Money { get; set; }

            [JsonProperty(PropertyName = "ServerRewards Points")]
            public int Points { get; set; }

            [JsonProperty(PropertyName = "SkillTree XP")]
            public double XP { get; set; }
        }

        public class SkinSettingsDefault
        {
            [JsonProperty(PropertyName = "Include Workshop Skins")]
            public bool RandomWorkshopSkins { get; set; } = true;

            [JsonProperty(PropertyName = "Preset Skin")]
            public ulong PresetSkin { get; set; }

            [JsonProperty(PropertyName = "Use Random Skin")]
            public bool RandomSkins { get; set; } = true;
        }

        public class SkinSettingsLoot
        {
            [JsonProperty(PropertyName = "Include Workshop Skins")]
            public bool RandomWorkshopSkins { get; set; } = true;

            [JsonProperty(PropertyName = "Use Random Skin")]
            public bool RandomSkins { get; set; } = true;

            [JsonProperty(PropertyName = "Use Imported Workshop Skins File")]
            public bool Imported { get; set; }
        }

        public class SkinSettingsDeployables
        {
            [JsonProperty(PropertyName = "Partial Names", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> Names { get; set; } = new List<string>
            {
                "door", "barricade", "chair", "fridge", "furnace", "locker", "reactivetarget", "rug", "sleepingbag", "table", "vendingmachine", "waterpurifier", "skullspikes", "skulltrophy", "summer_dlc", "sled"
            };

            [JsonProperty(PropertyName = "Preset Door Skins", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<ulong> Doors { get; set; } = new List<ulong>();

            [JsonProperty(PropertyName = "Include Workshop Skins")]
            public bool RandomWorkshopSkins { get; set; } = true;

            [JsonProperty(PropertyName = "Use Random Skin")]
            public bool RandomSkins { get; set; } = true;

            [JsonProperty(PropertyName = "Skin Everything")]
            public bool Everything { get; set; } = true;
        }

        public class SkinSettings
        {
            [JsonProperty(PropertyName = "Boxes")]
            public SkinSettingsDefault Boxes { get; set; } = new SkinSettingsDefault();

            [JsonProperty(PropertyName = "Loot Items")]
            public SkinSettingsLoot Loot { get; set; } = new SkinSettingsLoot();

            [JsonProperty(PropertyName = "Deployables")]
            public SkinSettingsDeployables Deployables { get; set; } = new SkinSettingsDeployables();

            [JsonProperty(PropertyName = "Randomize Npc Item Skins")]
            public bool Npcs { get; set; } = true;

            [JsonProperty(PropertyName = "Use Identical Skins For All Npcs")]
            public bool UniqueNpcs { get; set; } = true;

            [JsonProperty(PropertyName = "Ignore If Skinned Already")]
            public bool IgnoreSkinned { get; set; } = true;
        }

        public class SkinSettingsImportedWorkshop
        {
            [JsonProperty(PropertyName = "Imported Workshop Skins", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public Dictionary<string, List<ulong>> SkinList { get; set; } = DefaultImportedSkins;
        }

        public class LootItem : IEquatable<LootItem>
        {
            [JsonProperty(PropertyName = "shortname")]
            public string shortname { get; set; }

            [JsonProperty(PropertyName = "name")]
            public string name { get; set; } = null;

            [JsonProperty(PropertyName = "amount")]
            public int amount { get; set; }

            [JsonProperty(PropertyName = "skin")]
            public ulong skin { get; set; }

            [JsonProperty(PropertyName = "amountMin")]
            public int amountMin { get; set; }

            [JsonProperty(PropertyName = "probability")]
            public float probability { get; set; } = 1f;

            [JsonProperty(PropertyName = "stacksize")]
            public int stacksize { get; set; } = -1;

            [JsonIgnore]
            private ItemDefinition _def { get; set; }

            [JsonIgnore]
            public ItemDefinition definition
            {
                get
                {
                    if (_def == null)
                    {
                        string _shortname = shortname.EndsWith(".bp") ? shortname.Replace(".bp", string.Empty) : shortname;

                        if (shortname.Contains("_") && ItemManager.FindItemDefinition(_shortname) == null)
                        {
                            _shortname = _shortname.Substring(_shortname.IndexOf("_") + 1);
                        }

                        _def = ItemManager.FindItemDefinition(_shortname);
                    }

                    return _def;
                }
            }

            [JsonIgnore]
            public bool isBlueprint { get; set; }

            [JsonIgnore]
            public bool isModified { get; set; }

            public LootItem() { }

            public LootItem(string shortname, int amountMin = 1, int amount = 1, ulong skin = 0, bool isBlueprint = false, float probability = 1.0f, int stacksize = -1, string name = null, bool isModified = false)
            {
                this.shortname = shortname;
                this.amountMin = amountMin;
                this.amount = amount;
                this.skin = skin;
                this.isBlueprint = isBlueprint;
                this.probability = probability;
                this.stacksize = stacksize;
                this.name = name;
                this.isModified = isModified;
            }

            public LootItem Clone()
            {
                return new LootItem(shortname, amountMin, amount, skin, isBlueprint, probability, stacksize, name, isModified);
            }

            public bool Equals(LootItem other)
            {
                return shortname == other.shortname && amount == other.amount && skin == other.skin && amountMin == other.amountMin;
            }

            public override bool Equals(object obj)
            {
                if (obj is LootItem)
                {
                    return Equals((LootItem)obj);
                }
                return false;
            }

            public override int GetHashCode()
            {
                return base.GetHashCode();
            }
        }

        public class TreasureSettings
        {
            [JsonProperty(PropertyName = "Resources Not Moved To Cupboards", ObjectCreationHandling = ObjectCreationHandling.Replace)]
            public List<string> ExcludeFromCupboard { get; set; } = new List<string>
            {
                "skull.human", "battery.small", "bone.fragments", "can.beans.empty", "can.tuna.empty", "water.salt", "water", "skull.wolf"
            };

            [JsonProperty(PropertyName = "Use Day Of Week Loot")]
            public bool UseDOWL { get; set; }

            [JsonProperty(PropertyName = "Do Not Duplicate Base Loot")]
            public bool UniqueBaseLoot { get; set; }

            [JsonProperty(PropertyName = "Do Not Duplicate Difficulty Loot")]
            public bool UniqueDifficultyLoot { get; set; }

            [JsonProperty(PropertyName = "Do Not Duplicate Default Loot")]
            public bool UniqueDefaultLoot { get; set; }

            [JsonProperty(PropertyName = "Use Stack Size Limit For Spawning Items")]
            public bool UseStackSizeLimit { get; set; }
        }

        public class UIBaseSettings
        {
            [JsonProperty(PropertyName = "Enabled", Order = 1)]
            public bool Enabled { get; set; } = true;

            [JsonProperty(PropertyName = "Anchor Min", Order = 2)]
            public string AnchorMin { get; set; }

            [JsonProperty(PropertyName = "Anchor Max", Order = 3)]
            public string AnchorMax { get; set; }

            [JsonProperty(PropertyName = "Panel Alpha", NullValueHandling = NullValueHandling.Ignore, Order = 4)]
            public float? PanelAlpha { get; set; } = 0.98f;

            [JsonProperty(PropertyName = "Panel Color", NullValueHandling = NullValueHandling.Ignore, Order = 5)]
            public string PanelColor { get; set; } = "#000000";
        }

        public class BuildingOptionsElevators : UIBaseSettings
        {
            public BuildingOptionsElevators()
            {
                AnchorMin = "0.406 0.915";
                AnchorMax = "0.59 0.949";
                PanelAlpha = 0f;
            }

            [JsonProperty(PropertyName = "Required Access Level", Order = 5)]
            public int RequiredAccessLevel { get; set; }

            [JsonProperty(PropertyName = "Required Access Level Grants Permanent Use", Order = 6)]
            public bool RequiredAccessLevelOnce { get; set; }

            [JsonProperty(PropertyName = "Required Keycard Skin ID", Order = 7)]
            public ulong SkinID { get; set; } = 2690554489;

            [JsonProperty(PropertyName = "Requires Building Permission", Order = 8)]
            public bool RequiresBuildingPermission { get; set; }

            [JsonProperty(PropertyName = "Button Health", Order = 9)]
            public float ButtonHealth { get; set; } = 1000f;

            [JsonProperty(PropertyName = "Elevator Health", Order = 10)]
            public float ElevatorHealth { get; set; } = 600f;
        }

        public class UIRaidDetailsSettings : UIBaseSettings
        {
            public UIRaidDetailsSettings()
            {
                AnchorMin = "0.748 0.228";
                AnchorMax = "0.986 0.248";
            }

            [JsonProperty(PropertyName = "Details Font Size", Order = 5)]
            public int FontSize { get; set; } = 10;

            [JsonProperty(PropertyName = "Label Color", Order = 6)]
            public string LabelColor { get; set; } = "#EAEAEA";

            [JsonProperty(PropertyName = "Negative Color", Order = 7)]
            public string NegativeColor { get; set; } = "#FF0000";

            [JsonProperty(PropertyName = "Positive Color", Order = 8)]
            public string PositiveColor { get; set; } = "#008000";
        }

        public class UIDelaySettings : UIBaseSettings
        {
            public UIDelaySettings()
            {
                AnchorMin = "0.472 0.172";
                AnchorMax = "0.55 0.311";
                Enabled = false;
            }

            [JsonProperty(PropertyName = "Text Color", Order = 5)]
            public string Foreground { get; set; } = "#FF0000";
        }

        public class UIAdvancedAlertSettings : UIBaseSettings
        {
            [JsonProperty(PropertyName = "Time Shown", Order = 5)]
            public float Time { get; set; } = 5f;

            public UIAdvancedAlertSettings()
            {
                AnchorMin = "0.35 0.85";
                AnchorMax = "0.65 0.95";
                PanelAlpha = null;
                PanelColor = null;
            }
        }

        public class UISettings
        {
            [JsonProperty(PropertyName = "Advanced Alerts UI")]
            public UIAdvancedAlertSettings AA { get; set; } = new UIAdvancedAlertSettings();

            [JsonProperty(PropertyName = "Delay")]
            public UIDelaySettings Delay { get; set; } = new UIDelaySettings();

            [JsonProperty(PropertyName = "Details")]
            public UIRaidDetailsSettings Details { get; set; } = new UIRaidDetailsSettings();

            [JsonProperty(PropertyName = "Enabled")]
            public bool Enabled { get; set; } = true;

            [JsonProperty(PropertyName = "Status Anchor Min")]
            public string AnchorMin { get; set; } = "0.748 0.249";

            [JsonProperty(PropertyName = "Status Anchor Max")]
            public string AnchorMax { get; set; } = "0.986 0.279";

            [JsonProperty(PropertyName = "Status Font Size")]
            public int FontSize { get; set; } = 12;

            [JsonProperty(PropertyName = "Panel Alpha")]
            public float PanelAlpha { get; set; } = 0.98f;

            [JsonProperty(PropertyName = "Panel Color")]
            public string PanelColor { get; set; } = "#000000";

            [JsonProperty(PropertyName = "PVP Color")]
            public string ColorPVP { get; set; } = "#FF0000";

            [JsonProperty(PropertyName = "PVE Color")]
            public string ColorPVE { get; set; } = "#008000";

            [JsonProperty(PropertyName = "Show Loot Left")]
            public bool Containers { get; set; } = true;

            [JsonProperty(PropertyName = "Show Time Left")]
            public bool Time { get; set; } = true;
        }

        public class WeaponTypeStateSettings
        {
            [JsonProperty(PropertyName = "AutoTurret")]
            public bool AutoTurret { get; set; } = true;

            [JsonProperty(PropertyName = "FlameTurret")]
            public bool FlameTurret { get; set; } = true;

            [JsonProperty(PropertyName = "FogMachine")]
            public bool FogMachine { get; set; } = true;

            [JsonProperty(PropertyName = "GunTrap")]
            public bool GunTrap { get; set; } = true;

            [JsonProperty(PropertyName = "SamSite")]
            public bool SamSite { get; set; } = true;
        }

        public class WeaponTypeAmountSettings
        {
            [JsonProperty(PropertyName = "AutoTurret")]
            public int AutoTurret { get; set; } = 256;

            [JsonProperty(PropertyName = "FlameTurret")]
            public int FlameTurret { get; set; } = 256;

            [JsonProperty(PropertyName = "FogMachine")]
            public int FogMachine { get; set; } = 5;

            [JsonProperty(PropertyName = "GunTrap")]
            public int GunTrap { get; set; } = 128;

            [JsonProperty(PropertyName = "SamSite")]
            public int SamSite { get; set; } = 24;
        }

        public class WeaponSettingsTeslaCoil
        {
            [JsonProperty(PropertyName = "Requires A Power Source")]
            public bool RequiresPower { get; set; } = true;

            [JsonProperty(PropertyName = "Max Discharge Self Damage Seconds (0 = None, 120 = Rust default)")]
            public float MaxDischargeSelfDamageSeconds { get; set; }

            [JsonProperty(PropertyName = "Max Damage Output")]
            public float MaxDamageOutput { get; set; } = 35f;

            [JsonProperty(PropertyName = "Health")]
            public float Health { get; set; } = 250f;
        }

        public class WeaponSettings
        {
            [JsonProperty(PropertyName = "Infinite Ammo")]
            public WeaponTypeStateSettings InfiniteAmmo { get; set; } = new WeaponTypeStateSettings();

            [JsonProperty(PropertyName = "Ammo")]
            public WeaponTypeAmountSettings Ammo { get; set; } = new WeaponTypeAmountSettings();

            [JsonProperty(PropertyName = "Tesla Coil")]
            public WeaponSettingsTeslaCoil TeslaCoil { get; set; } = new WeaponSettingsTeslaCoil();

            [JsonProperty(PropertyName = "Fog Machine Allows Motion Toggle")]
            public bool FogMotion { get; set; } = true;

            [JsonProperty(PropertyName = "Fog Machine Requires A Power Source")]
            public bool FogRequiresPower { get; set; } = true;

            [JsonProperty(PropertyName = "SamSite Repairs Every X Minutes (0.0 = disabled)")]
            public float SamSiteRepair { get; set; } = 5f;

            [JsonProperty(PropertyName = "SamSite Range (350.0 = Rust default)")]
            public float SamSiteRange { get; set; } = 75f;

            [JsonProperty(PropertyName = "SamSite Requires Power Source")]
            public bool SamSiteRequiresPower { get; set; }

            [JsonProperty(PropertyName = "Spooky Speakers Requires Power Source")]
            public bool SpookySpeakersRequiresPower { get; set; }

            [JsonProperty(PropertyName = "Test Generator Power")]
            public float TestGeneratorPower { get; set; } = 100f;
        }

        public class Configuration
        {
            [JsonProperty(PropertyName = "Settings")]
            public PluginSettings Settings = new PluginSettings();

            [JsonProperty(PropertyName = "Event Messages")]
            public EventMessageSettings EventMessages = new EventMessageSettings();

            [JsonProperty(PropertyName = "GUIAnnouncements")]
            public GUIAnnouncementSettings GUIAnnouncement = new GUIAnnouncementSettings();

            [JsonProperty(PropertyName = "Ranked Ladder")]
            public RankedLadderSettings RankedLadder = new RankedLadderSettings();

            [JsonProperty(PropertyName = "Skins")]
            public SkinSettings Skins = new SkinSettings();

            [JsonProperty(PropertyName = "Treasure")]
            public TreasureSettings Treasure = new TreasureSettings();

            [JsonProperty(PropertyName = "UI")]
            public UISettings UI = new UISettings();

            [JsonProperty(PropertyName = "Weapons")]
            public WeaponSettings Weapons = new WeaponSettings();
        }

        //private bool isConfigurationInitialized;

        //private void AbortInitialization()
        //{
        //    Puts("ERROR! YOU HAVE INSTALLED THE FREE VERSION OVER THE TOP OF THE PREMIUM VERSION! ABORTED");
        //    isConfigurationInitialized = false;
        //    NextTick(() => Interface.Oxide.UnloadPlugin(Name));
        //}

        protected override void LoadConfig()
        {
            base.LoadConfig();
            try
            {
                config = Config.ReadObject<Configuration>();
                if (config == null) throw new Exception();
                //isConfigurationInitialized = true;
                //SaveConfig();
            }
            catch (Exception ex)
            {
                Puts("{0}", ex);
                LoadDefaultConfig();
            }
            //if (Config.Get("Settings", "Raid Management", "Assign Lockout When Lock Treasure Max Inactive Time Expires") != null)
            //{
            //    AbortInitialization();
            //    return;
            //}
            if (config.Settings.Management.AdditionalBlockedColliders.Remove("cube_"))
            {
                config.Settings.Management.AdditionalBlockedColliders.Add("cubes");
            }
            //if (isConfigurationInitialized)
            //{
            //    SaveConfig();
            //}
            UndoDeployables = config.Settings.Management.DoNotDestroyDeployables;
            UndoStructures = config.Settings.Management.DoNotDestroyStructures;
            UndoMounts = config.Settings.Management.DespawnMounts;
        }

        public static List<LootItem> TreasureLoot
        {
            get
            {
                List<LootItem> lootList;
                if (!Instance.Buildings.DifficultyLootLists.TryGetValue(RaidableMode.Random, out lootList))
                {
                    Instance.Buildings.DifficultyLootLists[RaidableMode.Random] = lootList = new List<LootItem>();
                }

                return lootList.ToList();
            }
        }

        public static List<LootItem> WeekdayLoot
        {
            get
            {
                List<LootItem> lootList;
                if (!config.Treasure.UseDOWL || !Instance.Buildings.WeekdayLootLists.TryGetValue(DateTime.Now.DayOfWeek, out lootList))
                {
                    Instance.Buildings.WeekdayLootLists[DateTime.Now.DayOfWeek] = lootList = new List<LootItem>();
                }

                return lootList.ToList();
            }
        }

        protected override void SaveConfig()
        {
            //if (isConfigurationInitialized)
            //{
                Config.WriteObject(config);
            //}
        }

        protected override void LoadDefaultConfig()
        {
            config = new Configuration();
            Puts("Loaded default configuration file");
        }

        #endregion

        #region UI

        public class UI // Credits: Absolut & k1lly0u
        {
            public static CuiElementContainer CreateElementContainer(string panelName, string color, string aMin, string aMax, bool cursor = false, string parent = "Overlay")
            {
                return new CuiElementContainer { { new CuiPanel { Image = { Color = color }, RectTransform = { AnchorMin = aMin, AnchorMax = aMax }, CursorEnabled = cursor }, new CuiElement().Parent = parent, panelName } };
            }

            public static void CreateLabel(ref CuiElementContainer container, string panel, string color, string text, int size, string aMin, string aMax, TextAnchor align = TextAnchor.MiddleCenter)
            {
                container.Add(new CuiLabel
                {
                    Text = { Color = color, FontSize = size, Align = align, FadeIn = 0f, Text = text },
                    RectTransform = { AnchorMin = aMin, AnchorMax = aMax, } //OffsetMin = "0.5 0.5", //OffsetMax = "0.5 0.5"
                }, panel);
            }

            private static double p(string hex, int j, int k)
            {
                int num;
                return int.TryParse(hex.TrimStart('#').Substring(j, k), NumberStyles.AllowHexSpecifier, NumberFormatInfo.CurrentInfo, out num) ? num : 1;
            }

            public static string Color(string hex, float a = 1.0f)
            {
                return $"{p(hex, 0, 2) / 255} {p(hex, 2, 2) / 255} {p(hex, 4, 2) / 255} {Mathf.Clamp(a, 0f, 1f)}";
            }

            public static void DestroyDelayUI(BasePlayer player)
            {
                if (player.IsReallyConnected() && Delay.Remove(player))
                {
                    CuiHelper.DestroyUi(player, DelayPanelName);
                    DestroyDelayUpdate(player);
                }
            }

            public static void DestroyStatusUI(BasePlayer player)
            {
                if (player.IsReallyConnected() && Players.Remove(player))
                {
                    CuiHelper.DestroyUi(player, StatusPanelName);
                    CuiHelper.DestroyUi(player, DetailsPanelName);
                    DestroyStatusUpdate(player);
                }
            }

            public static void DestroyAll()
            {
                foreach (var player in BasePlayer.activePlayerList)
                {
                    if (Players.Contains(player))
                    {
                        CuiHelper.DestroyUi(player, StatusPanelName);
                        CuiHelper.DestroyUi(player, DetailsPanelName);
                    }
                    if (Delay.Contains(player))
                    {
                        CuiHelper.DestroyUi(player, DelayPanelName);
                    }
                }
                Delay.Clear();
                Players.Clear();
                InvokeTimers.Clear();
            }

            private static void ShowDelayUI(BasePlayer player)
            {
                if (player.IsKilled())
                {
                    return;
                }

                DelaySettings ds;
                if (!Instance.PvpDelay.TryGetValue(player.userID, out ds))
                {
                    return;
                }

                if (ds.time <= 0)
                {
                    if (ds.Timer != null && !ds.Timer.Destroyed)
                    {
                        ds.Timer.Callback.Invoke();
                        ds.Timer.Destroy();
                    }

                    Instance.PvpDelay.Remove(player.userID);
                    DestroyDelayUI(player);
                    return;
                }

                if (Instance.EventTerritory(player.transform.position))
                {
                    return;
                }

                var ui = config.UI.Delay;

                CreateDelayUI(player, DelayPanelName, ds.time.ToString(), ui.Foreground, Color(ui.PanelColor, ui.PanelAlpha.Value), ui.AnchorMin, ui.AnchorMax);

                ds.time--;

                Delay.Add(player);
            }

            private static void CreateDelayUI(BasePlayer player, string panelName, string text, string color, string panelColor, string aMin, string aMax)
            {
                var element = CreateElementContainer(panelName, panelColor, aMin, aMax, false, "Hud");

                CreateLabel(ref element, panelName, Color(color), text, config.UI.FontSize, "0 0", "1 1");
                CuiHelper.AddUi(player, element);
            }

            public static void UpdateDelayUI(BasePlayer player)
            {
                Delay.RemoveAll(x => !x.IsReallyConnected());

                if (!player.IsReallyConnected())
                {
                    return;
                }

                DestroyDelayUI(player);

                if (config == null || !config.UI.Delay.Enabled)
                {
                    return;
                }

                ShowDelayUI(player);
                SetDelayUpdate(player);
            }

            private static void SetDelayUpdate(BasePlayer player)
            {
                Timers timers;
                if (!InvokeTimers.TryGetValue(player.userID, out timers))
                {
                    InvokeTimers[player.userID] = timers = new Timers();
                }

                if (timers.Delay == null || timers.Delay.Destroyed)
                {
                    timers.Delay = Instance.timer.Once(1f, () => UpdateDelayUI(player));
                }
                else timers.Delay.Reset();
            }

            public static void DestroyDelayUpdate(BasePlayer player)
            {
                Timers timers;
                if (InvokeTimers.TryGetValue(player.userID, out timers) && timers.Delay != null && !timers.Delay.Destroyed)
                {
                    timers.Delay.Destroy();
                }
            }

            private static void CreateStatus(BasePlayer player, RaidableBase raid, string panelName, string text, string color, string panelColor, string aMin, string aMax, int fontSize = 0)
            {
                var element = CreateElementContainer(panelName, panelColor, aMin, aMax, false, "Hud");

                CreateLabel(ref element, panelName, Color(color), text, fontSize == 0 ? config.UI.FontSize : fontSize, "0 0", "1 1");
                Players.Remove(player);
                CuiHelper.DestroyUi(player, panelName);
                CuiHelper.AddUi(player, element);
                Players.Add(player);
            }

            private static void ShowStatus(BasePlayer player)
            {
                var raid = RaidableBase.Get(player.transform.position);

                if (raid == null)
                {
                    return;
                }

                var ui = config.UI;
                string zone = raid.AllowPVP ? mx("PVP ZONE", player.UserIDString) : mx("PVE ZONE", player.UserIDString);
                float seconds = raid.despawnTime - Time.time;
                string despawnText = config.Settings.Management.DespawnMinutesInactive > 0 && seconds > 0 ? Math.Floor(TimeSpan.FromSeconds(seconds).TotalMinutes).ToString() : null;
                int lootAmount = raid._containers.Where(x => !x.IsKilled() && !raid.IsProtectedWeapon(x)).Sum(x => x.inventory.itemList.Count);
                string text;

                if (ui.Containers && ui.Time && !string.IsNullOrEmpty(despawnText))
                {
                    text = mx("UI Format", player.UserIDString, zone, lootAmount, despawnText);
                }
                else if (ui.Containers)
                {
                    text = mx("UI FormatContainers", player.UserIDString, zone, lootAmount);
                }
                else if (ui.Time && !string.IsNullOrEmpty(despawnText))
                {
                    text = mx("UI FormatMinutes", player.UserIDString, zone, despawnText);
                }
                else text = zone;

                CreateStatus(player, raid, StatusPanelName, text, raid.AllowPVP ? ui.ColorPVP : ui.ColorPVE, Color(ui.PanelColor, ui.PanelAlpha), ui.AnchorMin, ui.AnchorMax);
                ShowStatusDetails(raid, player);
            }

            private static void ShowStatusDetails(RaidableBase raid, BasePlayer player)
            {
                var ui = config.UI.Details;

                if (!ui.Enabled)
                {
                    return;
                }

                _sb.Clear();

                if (config.Settings.Management.UseOwners)
                {
                    string ownerColor = ui.NegativeColor;
                    string ownerLabel = mx("None", player.UserIDString);

                    if (raid.ownerId.IsSteamId())
                    {
                        if (raid.ownerId == player.userID)
                        {
                            ownerColor = ui.PositiveColor;
                            ownerLabel = mx("You", player.UserIDString);
                        }
                        else if (raid.IsAlly(raid.ownerId, player.userID))
                        {
                            ownerColor = ui.PositiveColor;
                            ownerLabel = mx("Ally", player.UserIDString);
                        }
                        else
                        {
                            ownerLabel = mx("Enemy", player.UserIDString);
                        }
                    }

                    _sb.Append(mx("OwnerFormat", player.UserIDString, ownerColor, ownerLabel));
                }

                if (config.Settings.Management.LockTime > 0f)
                {
                    string statusColor = ui.PositiveColor;
                    string status = mx("Active", player.UserIDString);
                    string inactiveTimeLeft = string.Empty;
                    float time = raid.GetRaider(player).lastActiveTime;
                    float secondsLeft = (config.Settings.Management.LockTime * 60f) - (Time.time - time);
                    if (secondsLeft > 0f)
                    {
                        inactiveTimeLeft = mx("InactiveTimeLeft", player.UserIDString, Math.Floor(TimeSpan.FromSeconds(secondsLeft).TotalMinutes).ToString());
                    }

                    if (string.IsNullOrEmpty(inactiveTimeLeft))
                    {
                        statusColor = ui.NegativeColor;
                        status = mx("Inactive", player.UserIDString);
                    }

                    _sb.Append(mx("Status:", player.UserIDString, statusColor, status, inactiveTimeLeft));
                }

                if (_sb.Length != 0)
                {
                    CreateStatus(player, raid, DetailsPanelName, _sb.ToString(), ui.LabelColor, Color(ui.PanelColor, ui.PanelAlpha.Value), ui.AnchorMin, ui.AnchorMax, ui.FontSize);
                    _sb.Clear();
                }
            }

            public static void UpdateStatusUI(RaidableBase raid)
            {
                raid.GetRaiders(false).ForEach(UpdateStatusUI);
            }

            public static void UpdateStatusUI(BasePlayer player)
            {
                Players.RemoveAll(x => !x.IsReallyConnected());

                if (config != null && player.IsReallyConnected())
                {
                    DestroyStatusUI(player);

                    if (config.UI.Enabled)
                    {
                        ShowStatus(player);
                        SetStatusUpdate(player);
                    }
                }
            }

            private static void SetStatusUpdate(BasePlayer player)
            {
                var raid = RaidableBase.Get(player.transform.position);

                if (raid == null || raid.IsDespawning)
                {
                    return;
                }

                Timers timers;
                if (!InvokeTimers.TryGetValue(player.userID, out timers))
                {
                    InvokeTimers[player.userID] = timers = new Timers();
                }

                if (timers.Status == null || timers.Status.Destroyed)
                {
                    timers.Status = Instance.timer.Once(60f, () => UpdateStatusUI(player));
                }
                else timers.Status.Reset();
            }

            public static void DestroyStatusUpdate(BasePlayer player)
            {
                Timers timers;
                if (InvokeTimers.TryGetValue(player.userID, out timers) && timers.Status != null && !timers.Status.Destroyed)
                {
                    timers.Status.Destroy();
                }
            }

            public const string DelayPanelName = "RB_UI_Delay";
            public const string StatusPanelName = "RB_UI_Status";
            public const string DetailsPanelName = "RB_UI_Details";

            public static List<BasePlayer> Delay = new List<BasePlayer>();
            public static List<BasePlayer> Players = new List<BasePlayer>();
            public static Dictionary<ulong, Timers> InvokeTimers = new Dictionary<ulong, Timers>();

            public class Timers
            {
                public Timer Delay;
                public Timer Status;
                public Timer Lockout;
            }
        }

        #endregion UI
    }
}

namespace Oxide.Plugins.RaidableBasesExtensionMethods
{
    public static class ExtensionMethods
    {
        internal static Core.Libraries.Permission p;
        public static bool All<T>(this IEnumerable<T> a, Func<T, bool> b) { foreach (T c in a) { if (!b(c)) { return false; } } return true; }
        public static int Average(this IList<int> a) { if (a.Count == 0) { return 0; } int b = 0; for (int i = 0; i < a.Count; i++) { b += a[i]; } return b / a.Count; }
        public static T ElementAt<T>(this IEnumerable<T> a, int b) { using (var c = a.GetEnumerator()) { while (c.MoveNext()) { if (b == 0) { return c.Current; } b--; } } return default(T); }
        public static bool Exists<T>(this HashSet<T> a) where T : BaseEntity { foreach (var b in a) { if (!b.IsKilled()) { return true; } } return false; }
        public static bool Exists<T>(this IEnumerable<T> a, Func<T, bool> b = null) { using (var c = a.GetEnumerator()) { while (c.MoveNext()) { if (b == null || b(c.Current)) { return true; } } } return false; }
        public static T FirstOrDefault<T>(this IEnumerable<T> a, Func<T, bool> b = null) { using (var c = a.GetEnumerator()) { while (c.MoveNext()) { if (b == null || b(c.Current)) { return c.Current; } } } return default(T); }
        public static void ForEach<T>(this IEnumerable<T> a, Action<T> action) { foreach (T n in a) { action(n); } }
        public static int RemoveAll<TKey, TValue>(this IDictionary<TKey, TValue> c, Func<TKey, TValue, bool> d) { int a = 0; foreach (var b in c.ToList()) { if (d(b.Key, b.Value)) { c.Remove(b.Key); a++; } } return a; }
        public static IEnumerable<V> Select<T, V>(this IEnumerable<T> a, Func<T, V> b) { var c = new List<V>(); using (var d = a.GetEnumerator()) { while (d.MoveNext()) { c.Add(b(d.Current)); } } return c; }
        public static string[] Skip(this string[] a, int b) { if (a.Length == 0) { return Array.Empty<string>(); } string[] c = new string[a.Length - b]; int n = 0; for (int i = 0; i < a.Length; i++) { if (i < b) continue; c[n] = a[i]; n++; } return c; }
        public static List<T> Take<T>(this IList<T> a, int b) { var c = new List<T>(); for (int i = 0; i < a.Count; i++) { if (c.Count == b) { break; } c.Add(a[i]); } return c; }
        public static Dictionary<T, V> ToDictionary<S, T, V>(this IEnumerable<S> a, Func<S, T> b, Func<S, V> c) { var d = new Dictionary<T, V>(); using (var e = a.GetEnumerator()) { while (e.MoveNext()) { d[b(e.Current)] = c(e.Current); } } return d; }
        public static List<T> ToList<T>(this IEnumerable<T> a) { return new List<T>(a); }
        public static IEnumerable<T> AsEnumerable<T>(this IEnumerable<T> a) => a;
        public static List<T> Where<T>(this IEnumerable<T> a, Func<T, bool> b) { var c = new List<T>(); using (var d = a.GetEnumerator()) { while (d.MoveNext()) { if (b(d.Current)) { c.Add(d.Current); } } } return c; }
        public static List<T> OfType<T>(this IEnumerable<BaseNetworkable> a) where T : BaseEntity { var b = new List<T>(); using (var c = a.GetEnumerator()) { while (c.MoveNext()) { if (c.Current is T) { b.Add(c.Current as T); } } } return b; }
        public static int Sum<T>(this IEnumerable<T> a, Func<T, int> b) { int c = 0; foreach (T d in a) { c = checked(c + b(d)); } return c; }
        public static bool HasPermission(this string a, string b) { if (p == null) { p = Interface.Oxide.GetLibrary<Core.Libraries.Permission>(null); } return !string.IsNullOrEmpty(a) && p.UserHasPermission(a, b); }
        public static bool HasPermission(this BasePlayer a, string b) { return a != null && a.UserIDString.HasPermission(b); }
        public static bool HasPermission(this ulong a, string b) { return a.ToString().HasPermission(b); }
        public static bool BelongsToGroup(this string a, string b) { if (p == null) { p = Interface.Oxide.GetLibrary<Core.Libraries.Permission>(null); } return !string.IsNullOrEmpty(a) && p.UserHasGroup(a, b); }
        public static bool BelongsToGroup(this BasePlayer a, string b) { return a != null && a.UserIDString.BelongsToGroup(b); }
        public static bool BelongsToGroup(this ulong a, string b) { return a.ToString().BelongsToGroup(b); }
        public static bool IsReallyConnected(this BasePlayer a) { return a.IsReallyValid() && a.net.connection != null; }
        public static bool IsKilled(this BaseNetworkable a) { return (object)a == null || a.IsDestroyed; }
        public static bool IsNull(this BaseNetworkable a) { return (object)a == null || a.IsDestroyed; }
        public static bool IsReallyValid(this BaseNetworkable a) { return !((object)a == null || a.IsDestroyed || (object)a.net == null); }
        public static void SafelyKill(this BaseNetworkable a) { if (a.IsKilled()) { return; } a.Kill(BaseNetworkable.DestroyMode.None); }
        public static bool CanCall(this Plugin o) { return (object)o != null && o.IsLoaded; }
        public static bool IsInBounds(this OBB o, Vector3 a) { return o.ClosestPoint(a) == a; }
        public static bool IsHuman(this BasePlayer a) { return !(a.IsNpc || !a.userID.IsSteamId()); }
        public static bool IsCheating(this BasePlayer a) { return a._limitedNetworking || a.IsFlying || a.UsedAdminCheat(30f) || a.IsGod() || a.metabolism?.calories?.min == 500; }
        public static BasePlayer ToPlayer(this IPlayer user) { return user.Object as BasePlayer; }
        public static bool IsOnLayerName(this Collider collider, string layerName) { try { return LayerMask.LayerToName(collider.gameObject.layer) == layerName; } catch { return false; } }
        public static string MaterialName(this Collider collider) { try { return collider.material.name; } catch { return string.Empty; } }
        public static string ObjectName(this Collider collider) { try { return collider.gameObject?.name ?? string.Empty; } catch { return string.Empty; } }
        public static Vector3 GetPosition(this Collider collider) { try { return collider.transform?.position ?? Vector3.zero; } catch { return Vector3.zero; } }
        public static string ObjectName(this BaseEntity entity) { try { return entity.name ?? string.Empty; } catch { return string.Empty; } }
        public static T GetRandom<T>(this HashSet<T> h) { if (h == null || h.Count == 0) { return default(T); } return h.ElementAt(UnityEngine.Random.Range(0, h.Count)); }
        public static int InventorySlots(this StorageContainer a) { if (a.IsKilled() || a.inventory == null) return 0; return a.inventorySlots; }
        public static float Distance(this Vector3 a, Vector3 b) => (a - b).magnitude;
        public static float Distance2D(this Vector3 a, Vector3 b) => (a.WithY(0f) - b.WithY(0f)).magnitude;
        public static float SqrDistance2D(this Vector3 a, Vector3 b) => (a.WithY(0f) - b.WithY(0f)).sqrMagnitude;
        public static bool IsMajorityDamage(this HitInfo hitInfo, DamageType damageType) => hitInfo?.damageTypes?.GetMajorityDamageType() == damageType;
        public static void ResetToPool<K, V>(this Dictionary<K, V> collection) { collection.Clear(); Pool.Free(ref collection); }
        public static void ResetToPool<T>(this HashSet<T> collection) { collection.Clear(); Pool.Free(ref collection); }
        public static void ResetToPool<T>(this List<T> collection) { collection.Clear(); Pool.Free(ref collection); }
    }
}
