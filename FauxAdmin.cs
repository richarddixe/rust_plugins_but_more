using Network;
using Facepunch;
using System;
using UnityEngine;
using Newtonsoft.Json;
using System.Collections;
using System.Collections.Generic;
using Oxide.Core.Plugins;
using Oxide.Core.Libraries.Covalence;

namespace Oxide.Plugins
{
    [Info("FauxAdmin", "Colon Blow", "2.0.0")]
    [Description("FauxAdmin")]

    public class FauxAdmin : CovalencePlugin
    {
        // Complete rewrite of plugin
        // Remember, player must disconnect and reconnect for Fauxadmins perms to take effect if they are logged in when granted.
        // And player must disconnect and reconnect if given god mode perms while logged in as well to take effect.
        // added a env.time command for fauxadmins to use if they have perms (not default)
        // and lots more. 
        // 6.12.23 update - added command for chat /noclip 

        #region Loadup

        private const string permAllowed = "fauxadmin.allowed"; //Grants player the FauxAdmin powers, that player must disconnect and reconnect to take effect.
        private const string permBypass = "fauxadmin.bypass"; //Allows specified FauxAdmin and (Blocked)Admins/Mods to noclip thru Non Auth TC's if config is enabled to Disable Globally.
        private const string permBlocked = "fauxadmin.blocked"; //Blocks specifed Real Admin or Mod from using a few commands. ie..Noclip..etc.
        private const string permGodMode = "fauxadmin.allowgod"; //Allows specified FauxAdmin, Admin or Mod to Use of GodMode, even if its Disabled Globally in config.
        private const string permGodBlock = "fauxadmin.blockgod"; //Blocks specified FauxAdmin, Admin or Mod to Use of GodMode, even if its Enabled Globally in config.
        private const string permAllowTime = "fauxadmin.allowtime"; //Allows specified FauxAdmin, Admin or Mod to Use of Env.Time commands, even if its not enabled Globally in config.
        private const string permAllowKill = "fauxadmin.allowkill"; //Allows specified FauxAdmin, Admin or Mod to Use of entkill command, even if its not enabled Globally in config.
        private const string permOnlyOwn = "fauxadmin.allowown"; //Allows Fauxadmin to only noclip ONLY under Authorized TC Zones.
        private const string permTerrain = "fauxadmin.allowterrain"; //Allows Fauxadmin to only noclip under Terrain if Disabled Globally in Config.
        private const string permCanLoot = "fauxadmin.canloot"; //Allows Fauxadmin to loot things when Disabled Globally in Config

        private void Loaded()
        {
            Unsubscribe(nameof(OnStructureDemolish));
            Unsubscribe(nameof(OnStructureRotate));
            Unsubscribe(nameof(OnStructureUpgrade));
            Unsubscribe(nameof(OnUserPermissionGranted));
            Unsubscribe(nameof(OnUserPermissionRevoked));
            Unsubscribe(nameof(CanLootEntity));
            permission.RegisterPermission(permAllowed, this);
            permission.RegisterPermission(permBypass, this);
            permission.RegisterPermission(permBlocked, this);
            permission.RegisterPermission(permGodMode, this);
            permission.RegisterPermission(permGodBlock, this);
            permission.RegisterPermission(permAllowTime, this);
            permission.RegisterPermission(permAllowKill, this);
            permission.RegisterPermission(permOnlyOwn, this);
            permission.RegisterPermission(permTerrain, this);
            permission.RegisterPermission(permCanLoot, this);
            LoadConfig();
        }

        private void OnServerInitialized()
        {
            if (config.fauxAdminSettings.DisableFauxAdminDemolish) Subscribe(nameof(OnStructureDemolish));
            if (config.fauxAdminSettings.DisableFauxAdminRotate) Subscribe(nameof(OnStructureRotate));
            if (config.fauxAdminSettings.DisableFauxAdminUpgrade) Subscribe(nameof(OnStructureUpgrade));
            if (config.fauxAdminSettings.MessageOnFauxAdminGrant) Subscribe(nameof(OnUserPermissionGranted));
            if (config.fauxAdminSettings.KickOnFauxAdminRevoke) Subscribe(nameof(OnUserPermissionRevoked));
            if (config.fauxAdminSettings.DisableLooting) Subscribe(nameof(CanLootEntity));

            ServerMgr.Instance.StartCoroutine(ProcessFuaxAdminControls());
        }

        #endregion

        #region Configuration

        private static PluginConfig config;

        private class PluginConfig
        {
            public FauxAdminSettings fauxAdminSettings { get; set; }

            public class FauxAdminSettings
            {
                [JsonProperty(PropertyName = "GodMode - Disable God Mode use for all Standard FauxAdmins (except those with fauxadmin.allowgod perms) ? (users must disconnect/reconnect to take effect) ")] public bool DisableGodMode { get; set; }
                [JsonProperty(PropertyName = "GodMode - Message player to disconect/reconnect when fauxadmin.allowgod perms are granted and they are in game ? (users must disconnect/reconnect to take effect) ")] public bool MessageOnGodGrant { get; set; }
                [JsonProperty(PropertyName = "GodMode - Force Disconnect of player when fauxadmin.allowgod perms are revoked and they are in game ? (users must disconnect/reconnect to take effect) ")] public bool KickOnGodRevoke { get; set; }

                [JsonProperty(PropertyName = "Command - Env.Time - Enable Use of Env.Time Admin command to set in game time, for all FauxAdmins ? (default false) ")] public bool EnableEnvTime { get; set; }
                [JsonProperty(PropertyName = "Command - EntKill - Enable Simulated Use of Admin Command (ent kill) for all FauxAdmins ? (default true)  ")] public bool EnableEntKill { get; set; }
                [JsonProperty(PropertyName = "Command - EntKill - Only Allow FauxAdmins to entkill there OWN stuff (default true) ? ")] public bool EntKillOnlyOwn { get; set; }

                [JsonProperty(PropertyName = "Noclip - Disallow FauxAdmins (unless they have the 'fauxadmin.bypass' permission) from using the Noclip (flying) feature in Tool Cupboard (TC) zones where they are not authorized, which are typically owned by other players. ")] public bool DisableNoclipOnNoBuild { get; set; }
                [JsonProperty(PropertyName = "Noclip - Allow the FauxAdmins to use the Noclip (flying) feature exclusively within Authorized Tool Cupboard (TC) Zones, thereby preventing them from flying in all other areas. ? ")] public bool EnableNoclipOnBuild { get; set; }

                [JsonProperty(PropertyName = "Antihack - Terrain Kill - Allow FauxAdmin to Fly underground without Antihack killing them (if disabled, FauxAdmin must have allowterrain perm or Godmode to fly underground) ?")] public bool EnableUnderGround { get; set; }
                [JsonProperty(PropertyName = "Looting - Disable FauxAdmin ability to loot things (boxes, containers, corpses..etc) ?")] public bool DisableLooting { get; set; }

                [JsonProperty(PropertyName = "Contruction - Disable FauxAdmin Ability to Demolish OTHER players building parts ? ")] public bool DisableFauxAdminDemolish { get; set; }
                [JsonProperty(PropertyName = "Contruction - Disable FauxAdmin Ability to Rotate OTHER players building parts ? ")] public bool DisableFauxAdminRotate { get; set; }
                [JsonProperty(PropertyName = "Contruction - Disable FauxAdmin Ability to Upgrade OTHER players building parts ? ")] public bool DisableFauxAdminUpgrade { get; set; }

                [JsonProperty(PropertyName = "Permissions - Grant - Message Online Player when Fauxadmin.allowed perms are granted (perms only take effect when disconnect/connect) ? ")] public bool MessageOnFauxAdminGrant { get; set; }
                [JsonProperty(PropertyName = "Permissions - Revoke - Disconnect Online Player when Fauxadmin.allowed perms are revoked (perms only take effect when disconnect/connect) ?")] public bool KickOnFauxAdminRevoke { get; set; }
                [JsonProperty(PropertyName = "Player Flag - Backend - Use (isAdmin) Instead of (isDeveloper) for FauxAdmin magic (default is dev, better compability with other plugins) ? ")] public bool UseAdminFlag { get; set; }
            }

            public static PluginConfig DefaultConfig() => new PluginConfig()
            {
                fauxAdminSettings = new PluginConfig.FauxAdminSettings
                {
                    DisableGodMode = false,
                    MessageOnGodGrant = true,
                    KickOnGodRevoke = true,
                    EnableEnvTime = false,
                    EnableEntKill = true,
                    EntKillOnlyOwn = true,
                    DisableNoclipOnNoBuild = true,
                    EnableNoclipOnBuild = false,
                    EnableUnderGround = true,
                    DisableLooting = false,
                    DisableFauxAdminDemolish = true,
                    DisableFauxAdminRotate = true,
                    DisableFauxAdminUpgrade = true,
                    UseAdminFlag = false,
                    MessageOnFauxAdminGrant = true,
                    KickOnFauxAdminRevoke = true,
                }
            };
        }

        protected override void LoadDefaultConfig()
        {
            PrintWarning("New configuration file created!!");
            config = PluginConfig.DefaultConfig();
        }
        protected override void LoadConfig()
        {
            base.LoadConfig();
            config = Config.ReadObject<PluginConfig>();
            SaveConfig();
        }
        protected override void SaveConfig()
        {
            Config.WriteObject(config);
        }

        #endregion

        #region Localization

        protected override void LoadDefaultMessages()
        {
            lang.RegisterMessages(new Dictionary<string, string>
            {
                ["notauthorized"] = "You are not authorized to use that command !!",
                ["disablegod"] = "You are not authorized to use God Mode !!",
                ["disablenoclip"] = "You are not allowed to noclip into a area you do not have TC priv.",
                ["processonconnect"] = "was processed as a FauxAdmin when they connceted.",
                ["processonload"] = "was processed as a FauxAdmin when plugin reloaded.",
                ["permgranted"] = "You have been granted Faux Admin, you must disconnect and reconnect to take effect.",
                ["permrevoked"] = "Faux Admin rights removed, You where disconnected.",
                ["godgranted"] = "You have been granted Admin God Mode, you must disconnect and reconnect to take effect.",
                ["godrevoked"] = "God Mode rights Removed, You where disconnected.",
            }, this);
        }

        #endregion

        #region Commands

        [Command("fly")]
        private void cmdfly(IPlayer iplayer, string command, string[] args)
        {
            var player = iplayer.Object as BasePlayer;
            ConsoleNetwork.SendClientCommand(player.net.connection, "noclip");
        }

        [Command("noclip")]
        private void cmdNoClip(IPlayer iplayer, string command, string[] args)
        {
            var player = iplayer.Object as BasePlayer;
            ConsoleNetwork.SendClientCommand(player.net.connection, "noclip");
        }

        [Command("entkill")]
        private void cmdEntKill(IPlayer iplayer, string command, string[] args)
        {
            var player = iplayer.Object as BasePlayer;
            if (player == null) return;

            // Must be a Standard Fauxadmin to continue checking
            if (!player.IPlayer.HasPermission(permAllowed)) return;

            if (config.fauxAdminSettings.EnableEntKill || player.IPlayer.HasPermission(permAllowKill))
            {
                EntKillProcess(player);
            }
            else player.IPlayer.Message(lang.GetMessage("notauthorized", this, player.IPlayer.Id));
        }

        #endregion

        #region Hooks

        private object OnClientCommand(Connection connection, string command)
        {
            //Puts("Debug1 : " + command);

            var player = BasePlayer.FindByID(connection.userid);
            if (player == null) return null;

            if (!player.IPlayer.HasPermission(permAllowed)) return null;

            if (command.Contains("setinfo \"global.god\" \"True\""))
            {
                if (!player.IPlayer.HasPermission(permGodMode))
                {
                    player.IPlayer.Message(lang.GetMessage("disablegod", this, player.IPlayer.Id));
                    return false;
                }
            }
            else if (command.Contains("env.time"))
            {
                if (config.fauxAdminSettings.EnableEnvTime || player.IPlayer.HasPermission(permAllowTime))
                {
                    string[] array = command.Split(' ');

                    if (array.Length > 1)
                    {
                        this.covalence.Server.Command("env.time " + array[1].ToString());
                        Puts($"{player} used the env.time command");
                    }
                    else
                    {
                        player.IPlayer.Message("Current Time is : " + TOD_Sky.Instance.Cycle.Hour.ToString());
                    }
                }
                else
                {
                    player.IPlayer.Message(lang.GetMessage("notauthorized", this, player.IPlayer.Id));
                }
            }

            return null;
        }

        private object CanLootEntity(BasePlayer player, BaseEntity container)
        {
            if (container is DroppedItemContainer || container is LootableCorpse || container is ResourceContainer || container is StorageContainer)
            {
                if (player.IPlayer.HasPermission(permAllowed) && !player.IPlayer.HasPermission(permCanLoot)) return true;
            }
            return null;
        }


        private void OnPlayerConnected(BasePlayer player)
        {
            ProcessPlayer(player);
        }

        private object CanUpdateSign(BasePlayer player, Signage sign)
        {
            if (player.IPlayer.HasPermission(permAllowed) && sign.OwnerID != player.userID)
            {
                return false;
            }
            return null;
        }

        private object OnStructureDemolish(BuildingBlock block, BasePlayer player)
        {
            if (player.IPlayer.HasPermission(permAllowed) && block.OwnerID.IsSteamId() && block.OwnerID != player.userID) return true;
            return null;
        }

        private object OnStructureRotate(BuildingBlock block, BasePlayer player)
        {
            if (player.IPlayer.HasPermission(permAllowed) && block.OwnerID.IsSteamId() && block.OwnerID != player.userID) return true;
            return null;
        }

        private object OnStructureUpgrade(BuildingBlock block, BasePlayer player)
        {
            if (player.IPlayer.HasPermission(permAllowed) && block.OwnerID.IsSteamId() && block.OwnerID != player.userID) return true;
            return null;
        }

        private void OnUserPermissionGranted(string id, string permName)
        {
            ulong playerid = Convert.ToUInt64(id);
            var player = BasePlayer.FindByID(playerid);
            if (player == null) return;
            if (config.fauxAdminSettings.MessageOnFauxAdminGrant && permName == permAllowed) player.IPlayer.Message(lang.GetMessage("permgranted", this, player.IPlayer.Id));
            if (config.fauxAdminSettings.MessageOnGodGrant && permName == permGodMode) player.IPlayer.Message(lang.GetMessage("godgranted", this, player.IPlayer.Id));
        }

        private void OnUserPermissionRevoked(string id, string permName)
        {
            ulong playerid = Convert.ToUInt64(id);
            var player = BasePlayer.FindByID(playerid);
            if (player == null) return;
            if (config.fauxAdminSettings.KickOnFauxAdminRevoke && permName == permAllowed) player.Kick(lang.GetMessage("permrevoked", this, player.IPlayer.Id));
            if (config.fauxAdminSettings.KickOnGodRevoke && permName == permGodMode) player.Kick(lang.GetMessage("godrevoked", this, player.IPlayer.Id));
        }

        private object OnPlayerViolation(BasePlayer player, AntiHackType type, float amount)
        {
            if (type == AntiHackType.FlyHack)
            {
                if (player.IPlayer.HasPermission(permAllowed)) return false;
            }
            if (type == AntiHackType.InsideTerrain)
            {
                if (config.fauxAdminSettings.EnableUnderGround) return false;
                if (player.IPlayer.HasPermission(permTerrain)) return false;
            }
            return null;
        }

        private void Unload()
        {
            DestroyAll<FauxAdminControl>();
        }

        #endregion

        #region Methods

        private void EntKillProcess(BasePlayer player)
        {
            RaycastHit RayHit;
            if (Physics.Raycast(player.eyes.HeadRay(), out RayHit, 10f, LayerMask.GetMask("Construction", "Deployed", "Default", "AI", "Player (Server)")))
            {
                var baseEntity = RayHit.GetEntity();
                if (baseEntity == null) return;
                if (baseEntity is BasePlayer || baseEntity.IsNpc) return;
                if (config.fauxAdminSettings.EntKillOnlyOwn && player.userID != baseEntity.OwnerID) return;
                baseEntity.Kill(BaseNetworkable.DestroyMode.Gib);
            }
        }

        private IEnumerator ProcessFuaxAdminControls()
        {
            foreach (var player in BasePlayer.activePlayerList)
            {
                var authLevel = player.net?.connection?.authLevel;
                if (authLevel != null && authLevel > 0 && !player.IPlayer.HasPermission(permBlocked)) continue;

                var hasAllowedPermission = player.IPlayer.HasPermission(permAllowed);
                var hasBypassPermission = player.IPlayer.HasPermission(permBypass);
                var hasGodBlockPermission = player.IPlayer.HasPermission(permGodBlock);
                var hasGodModePermission = player.IPlayer.HasPermission(permGodMode);

                if (hasAllowedPermission)
                {
                    if (!hasBypassPermission)
                    {
                        var controls = player.GetComponent<FauxAdminControl>();
                        if (!controls)
                        {
                            player.gameObject.AddComponent<FauxAdminControl>();
                            Puts($"{player} " + lang.GetMessage("processonload", this, player.IPlayer.Id));
                        }
                    }
                    if (hasGodBlockPermission || (config.fauxAdminSettings.DisableGodMode && !hasGodModePermission))
                    {
                        ConsoleNetwork.SendClientCommand(player.net.connection, "setinfo \"global.god\" \"False\"");
                        Puts($"{player} " + lang.GetMessage("processonload", this, player.IPlayer.Id));
                    }
                }
                yield return new WaitForEndOfFrame();
            }
        }


        private void ProcessPlayer(BasePlayer player)
        {
            if (player.net?.connection?.authLevel > 0)
            {
                if (player.IPlayer.HasPermission(permBlocked))
                {
                    player.SetPlayerFlag(BasePlayer.PlayerFlags.IsDeveloper, false);
                    player.SetPlayerFlag(BasePlayer.PlayerFlags.IsAdmin, false);
                    if (player.IPlayer.HasPermission(permGodBlock) || (config.fauxAdminSettings.DisableGodMode && !player.IPlayer.HasPermission(permGodMode)))
                    {
                        ConsoleNetwork.SendClientCommand(player.net.connection, "setinfo \"global.god\" \"False\"");
                    }
                }
            }
            else if (!player.IPlayer.HasPermission(permAllowed))
            {
                player.SetPlayerFlag(BasePlayer.PlayerFlags.IsAdmin, false);
                player.SetPlayerFlag(BasePlayer.PlayerFlags.IsDeveloper, false);
            }
            else
            {
                player.SetPlayerFlag(BasePlayer.PlayerFlags.IsAdmin, config.fauxAdminSettings.UseAdminFlag);
                player.SetPlayerFlag(BasePlayer.PlayerFlags.IsDeveloper, !config.fauxAdminSettings.UseAdminFlag);
                if (player.IPlayer.HasPermission(permGodBlock) || (config.fauxAdminSettings.DisableGodMode && !player.IPlayer.HasPermission(permGodMode)))
                {
                    ConsoleNetwork.SendClientCommand(player.net.connection, "setinfo \"global.god\" \"False\"");
                }
                if (!player.IPlayer.HasPermission(permBypass))
                {
                    var hasControls = player.GetComponent<FauxAdminControl>();
                    if (hasControls) hasControls.OnDestroy();
                    var addControls = player.gameObject.AddComponent<FauxAdminControl>();
                }
            }
            Puts($"{player} " + lang.GetMessage("processonconnect", this, player.IPlayer.Id));
        }


        private static void DestroyAll<T>()
        {
            var objects = GameObject.FindObjectsOfType(typeof(T));
            if (objects != null)
                foreach (var gameObj in objects)
                    GameObject.Destroy(gameObj);
        }

        #endregion

        #region FauxAdmin Control

        private class FauxAdminControl : FacepunchBehaviour
        {
            FauxAdmin instance = new FauxAdmin();
            private BasePlayer player;
            private bool hasFrozenPosition;

            private void Awake()
            {
                player = GetComponent<BasePlayer>();
                if (player == null) { OnDestroy(); return; }
                hasFrozenPosition = false;
            }

            private void DeactivateNoClip(BasePlayer player)
            {
                if (hasFrozenPosition) return;
                if (player.IPlayer.HasPermission(permBypass)) return;
                hasFrozenPosition = true;
                ServerMgr.Instance.StartCoroutine(DeactivateAndFreeze());
            }

            private IEnumerator DeactivateAndFreeze()
            {
                GenericPosition pos = player.IPlayer.Position();

                ConsoleNetwork.SendClientCommand(player.net.connection, "noclip");
                player.IPlayer.Message(instance.lang.GetMessage("disablenoclip", instance, player.IPlayer.Id));

                // Repeatedly teleport the player to the same position
                for (int i = 0; i < 8; i++)
                {
                    yield return new WaitForSeconds(0.1f);
                    player.IPlayer.Teleport(pos.X, pos.Y, pos.Z);
                }

                yield return new WaitForSeconds(0.1f);
                hasFrozenPosition = false;
            }


            private bool PlayerIsInOwnTCRange()
            {
                List<BuildingPrivlidge> privList = Pool.GetList<BuildingPrivlidge>();

                Vis.Entities<BuildingPrivlidge>(player.transform.position, 50f, privList);

                foreach (BuildingPrivlidge foundEnt in privList)
                {
                    if (foundEnt.IsAuthed(player))
                    {
                        Pool.FreeList<BuildingPrivlidge>(ref privList);
                        return true;
                    }
                }

                Pool.FreeList<BuildingPrivlidge>(ref privList);
                return false;
            }


            private void FixedUpdate()
            {
                if (player == null) { Destroy(gameObject); return; }

                if (player.IsFlying && !hasFrozenPosition)
                {
                    if (config.fauxAdminSettings.EnableNoclipOnBuild || player.IPlayer.HasPermission(permOnlyOwn))
                    {
                        if (!PlayerIsInOwnTCRange()) DeactivateNoClip(player);
                    }
                    else if (config.fauxAdminSettings.DisableNoclipOnNoBuild)
                    {
                        if (player.IsBuildingBlocked()) DeactivateNoClip(player);
                    }
                }
            }


            public void OnDestroy()
            {
                GameObject.Destroy(this);
            }
        }

        #endregion
    }
}