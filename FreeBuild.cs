using System;
using System.Collections.Generic;

using Oxide.Core.Libraries.Covalence;

using Newtonsoft.Json;

/*
 * Thanks to WhiteThunder for helping with the hidden fake resources
 */

namespace Oxide.Plugins
{
    [Info("Free Build", "0x89A", "2.1.1")]
    [Description("Allows building, upgrading and placing deployables for free")]
    class FreeBuild : CovalencePlugin
    {
        private const string usePerm = "freebuild.allow";

        private const int _itemStartPosition = 24;

        private readonly HashSet<BasePlayer> _activePlayers = new HashSet<BasePlayer>();

        private readonly string[] _resourceItemShortnames =
        {
            "wood",
            "stones",
            "metal.fragments",
            "metal.refined"
        };
        
        private readonly List<Item> _resourceItems = new List<Item>();

        private void Init()
        {
            if (!_config.giveHiddenResources)
            {
                Unsubscribe(nameof(OnInventoryNetworkUpdate));
            }
            
            permission.RegisterPermission(usePerm, this);

            if (_config.requireChat)
            {
                AddCovalenceCommand(_config.chatCommand, nameof(Command), usePerm);
            }
        }

        private void Unload()
        {
            if (!_config.giveHiddenResources)
            {
                return;
            }

            foreach (BasePlayer player in _activePlayers)
            {
                player.inventory.SendUpdatedInventory(PlayerInventory.Type.Main, player.inventory.containerMain);
            }
        }

        #region -Hooks-

        private void OnEntitySaved(BasePlayer player, BaseNetworkable.SaveInfo saveInfo)
        {
            if (!IsAllowed(player))
            {
                return;
            }

            AddItems(saveInfo.msg.basePlayer.inventory.invMain);
        }

        private void OnInventoryNetworkUpdate(PlayerInventory inventory, ItemContainer container, ProtoBuf.UpdateItemContainer updatedItemContainer, PlayerInventory.Type inventoryType, bool sendToEveryone)
        {
            if (inventory != null && inventory.baseEntity != null && !IsAllowed(inventory.baseEntity))
            {
                return;
            }

            if (inventoryType == PlayerInventory.Type.Main)
            {
                AddItems(updatedItemContainer.container[0]);
            }
        }

        private object CanAffordUpgrade(BasePlayer player, BuildingBlock block, BuildingGrade.Enum iGrade)
        {
            if (IsAllowed(player))
            {
                return true;
            }
            
            return null;
        }
        
        object CanAffordToPlace(BasePlayer player, Planner planner, Construction construction)
        {
            if (IsAllowed(player))
            {
                return true;
            }
            
            return null;
        }

        object OnPayForPlacement(BasePlayer player, Planner planner, Construction construction)
        {
            if (IsAllowed(player) && DeployableCheck(construction.deployable))
            {
                return true;
            }
            
            return null;
        }

        object OnPayForUpgrade(BasePlayer player, BuildingBlock block, ConstructionGrade gradeTarget)
        {
            if (IsAllowed(player))
            {
                return true;
            }
            
            return null;
        }

        #endregion

        #region -Methods-

        private void Command(IPlayer iplayer, string command, string[] args)
        {
            BasePlayer player = iplayer.Object as BasePlayer;
            if (player == null) return;

            if (_activePlayers.Contains(player))
            {
                _activePlayers.Remove(player);
                player.ChatMessage(lang.GetMessage("Disabled", this, player.UserIDString));
            }
            else
            {
                _activePlayers.Add(player);
                player.ChatMessage(lang.GetMessage("Enabled", this, player.UserIDString));
            }
            
            player.inventory.SendUpdatedInventory(PlayerInventory.Type.Main, player.inventory.containerMain);
        }

        private bool IsAllowed(BasePlayer player)
        {
            return _config.requireChat ? _activePlayers.Contains(player) : permission.UserHasPermission(player.UserIDString, usePerm);
        }

        private bool DeployableCheck(Deployable deployable)
        {
            return !(deployable != null && !_config.freeDeployables && deployable.fullName.Contains("deployed"));
        }
        
        private void AddItems(ProtoBuf.ItemContainer containerData)
        {
            if (containerData == null)
            {
                return;
            }

            List<Item> items = GetItems();
            
            foreach (Item item in items)
            {
                containerData.contents.Add(item.Save());
            }
            
            containerData.slots = _itemStartPosition + items.Count;
        }
        
        private List<Item> GetItems()
        {
            if (_resourceItems.Count > 0)
            {
                return _resourceItems;
            }

            _resourceItems.Clear();
            
            int position = _itemStartPosition;
            foreach (string shortname in _resourceItemShortnames)
            {
                Item item = ItemManager.CreateByName(shortname, 10000);
                if (item == null)
                {
                    continue;
                }

                item.position = position++;
                _resourceItems.Add(item);
            }

            return _resourceItems;
        }

        #endregion

        protected override void LoadDefaultMessages()
        {
            lang.RegisterMessages(new Dictionary<string, string>
            {
                ["Enabled"] = "Free build <color=green>enabled</color>",
                ["Disabled"] = "Free build <color=red>disabled</color>",
            }, this);
        }
        
        #region -Configuration-

        private Configuration _config;

        private class Configuration
        {
            [JsonProperty("Chat Command")]
            public string chatCommand = "freebuild";
        
            [JsonProperty("Require Chat Command")]
            public bool requireChat = true;
            
            [JsonProperty("Free Deployables")]
            public bool freeDeployables = true;

            [JsonProperty("Give Player Hidden Resources")]
            public bool giveHiddenResources = true;
        }

        protected override void LoadConfig()
        {
            base.LoadConfig();
            try
            {
                _config = Config.ReadObject<Configuration>();
                if (_config == null) throw new Exception();
                SaveConfig();
            }
            catch
            {
                PrintError("Failed to load config, using default values");
                LoadDefaultConfig();
            }
        }

        protected override void LoadDefaultConfig() => _config = new Configuration();

        protected override void SaveConfig() => Config.WriteObject(_config);

        #endregion
    }
}