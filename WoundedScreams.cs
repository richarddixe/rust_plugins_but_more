using System.Collections.Generic;

namespace Oxide.Plugins
{
    [Info("Wounded Screams", "Death", "2.2.3")]
    [Description("Restored scream when a player is wounded")]

    class WoundedScreams : RustPlugin
    {
        #region Declarations
        Dictionary<ulong, Timer> Collection = new Dictionary<ulong, Timer>();
        const string exclude = "woundedscreams.exclude";
        const string nocooldown = "woundedscreams.nocooldown";
        const string ondemand = "woundedscreams.ondemand";
        bool Sub;
        Timer Get;
        #endregion

        #region Hooks
        void Init()
        {
            LoadConfigVariables();
            Unsub();
            permission.RegisterPermission(exclude, this);
            permission.RegisterPermission(ondemand, this);
            permission.RegisterPermission(nocooldown, this);
        }

        void Unload()
        {
            foreach (var entry in Collection)
            {
                Collection[entry.Key].Destroy();
            }
        }

        object OnPlayerWound(BasePlayer p)
        {
            if (permission.UserHasPermission(p.UserIDString, exclude))
            {
                return null;
            }

            PlayFX(p);

            if (!Sub)
            {
                Subscribe("OnEntityDeath");
                Subscribe("OnPlayerDisconnected");
                Sub = true;
            }
            return null;
        }

        void OnEntityDeath(BaseCombatEntity e) => Destroy(e as BasePlayer);
        void OnPlayerDisconnected(BasePlayer p) => Destroy(p);
        #endregion

        #region Functions
        void PlayFX(BasePlayer p)
        {
            Effect.server.Run(configData.Options.FX_Sound, p.transform.position);

            if (!Collection.ContainsKey(p.userID))
            {
                Collection.Add(p.userID, timer.Every(configData.Options.Interval, () =>
                {
                    if (p.IsWounded())
                    {
                        PlayFX(p);
                    }
                    else
                    {
                        Destroy(p);
                    }
                }
                ));
            }
        }

        void Destroy(BasePlayer p)
        {
            if (p != null && Collection.TryGetValue(p.userID, out Get))
            {
                Get.Destroy();
                Collection.Remove(p.userID);
            }

            if (Collection.Count == 0)
            {
                Unsub();
            }
        }

        void Unsub()
        {
            Unsubscribe("OnEntityDeath");
            Unsubscribe("OnPlayerDisconnected");
            Sub = false;
        }

        #region Commands
        [ConsoleCommand("scream")]
        void ConsoleCommand(ConsoleSystem.Arg arg) => ChatCommand(arg.Connection?.player as BasePlayer);

        [ChatCommand("scream")]
        void ChatCommand(BasePlayer p)
        {
            if (p == null)
            {
                return;
            }

            if (configData.Options.Enable_Scream_Ondemand && permission.UserHasPermission(p.UserIDString, ondemand))
            {
                if (Collection.ContainsKey(p.userID))
                {
                    SendReply(p, lang.GetMessage("cooldown", this, p.UserIDString).Replace("{0}", configData.Options.Scream_Cooldown.ToString()));
                }
                else
                {
                    Collection.Add(p.userID, timer.Once((permission.UserHasPermission(p.UserIDString, nocooldown)) ? 0 : configData.Options.Scream_Cooldown, () =>
                    {
                        if (Collection.ContainsKey(p.userID))
                        {
                            Collection.Remove(p.userID);
                        }
                    }
                    ));
                    PlayFX(p);
                }
            }
            else
            {
                SendReply(p, lang.GetMessage("noperm", this, p.UserIDString));
            }
        }
        #endregion

        #endregion

        #region Config
        private ConfigData configData;

        class ConfigData
        {
            public Options Options = new Options();
        }

        class Options
        {
            public bool Enable_Scream_Ondemand = false;
            public string FX_Sound = "assets/bundled/prefabs/fx/player/beartrap_scream.prefab";
            public float Interval = 6;
            public float Scream_Cooldown = 30;
        }

        private void LoadConfigVariables()
        {
            configData = Config.ReadObject<ConfigData>();
            SaveConfig(configData);
        }

        protected override void LoadDefaultConfig()
        {
            var config = new ConfigData();
            SaveConfig(config);
        }

        void SaveConfig(ConfigData config) => Config.WriteObject(config, true);
        #endregion

        #region Localization
        protected override void LoadDefaultMessages()
        {
            lang.RegisterMessages(new Dictionary<string, string>()
            {
                {"cooldown", "Please wait {0} seconds before trying to scream again." },
                {"noperm", "You do not have permission or this command is disabled." }
            }, this, "en");
        }
        private string msg(string key, string id = null) => lang.GetMessage(key, this, id);
        #endregion
    }
}