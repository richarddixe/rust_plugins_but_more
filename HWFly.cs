using UnityEngine;
using System.Collections.Generic;

namespace Oxide.Plugins
{
    [Info("HW Fly", "klauz24", "1.2.4"), Description("Allows players with permissions to fly around.")]
    internal class HWFly : HurtworldPlugin
    {
        private Dictionary<string, float> _flying = new Dictionary<string, float>();

        private float _defaultFlySpeed = 75.0f;

        private string _perm = "hwfly.allowed";

        protected override void LoadDefaultMessages()
        {
            lang.RegisterMessages(new Dictionary<string, string>
            {
                {"Prefix", "<color=lightblue>[HW Fly]</color>"},
                {"NoPerm", "You got no permission to use this command."},
                {"Enabled", "Enabled."},
                {"Disabled", "Disabled."},
                {"Speed", "Fly speed set to {0}."}
            }, this);
        }

        [ChatCommand("fly")]
        private void FlyCommand(PlayerSession session, string command, string[] args)
        {
            if (session.IsAdmin || permission.UserHasPermission(GetID64(session), _perm))
            {
                if (args.Length == 0)
                {
                    if (_flying.ContainsKey(GetID64(session)))
                    {
                        _flying.Remove(GetID64(session));
                        hurt.SendChatMessage(session, GetLang(session, "Prefix"), GetLang(session, "Disabled"));
                    }
                    else
                    {
                        _flying.Add(GetID64(session), _defaultFlySpeed);
                        hurt.SendChatMessage(session, GetLang(session, "Prefix"), GetLang(session, "Enabled"));
                    }
                }
                if (args.Length >= 1)
                {
                    float speed;
                    if (float.TryParse(args[0], out speed))
                    {
                        if (_flying.ContainsKey(GetID64(session)))
                        {
                            _flying[GetID64(session)] = speed;
                            hurt.SendChatMessage(session, GetLang(session, "Prefix"), string.Format(GetLang(session, "Speed"), speed));
                        }
                        else
                        {
                            _flying.Add(GetID64(session), speed);
                            hurt.SendChatMessage(session, GetLang(session, "Prefix"), GetLang(session, "Enabled"));
                        }
                        hurt.SendChatMessage(session, GetLang(session, "Prefix"), string.Format(GetLang(session, "Speed"), speed));
                    }
                }
            }
            else
            {
                hurt.SendChatMessage(session, GetLang(session, "Prefix"), GetLang(session, "NoPerm"));
            }
        }

        private void Init() => permission.RegisterPermission(_perm, this);

        private object OnPlayerTakeDamage(PlayerSession session, EntityEffectSourceData source)
        {
            if (_flying.ContainsKey(GetID64(session)))
            {
                return 0f;
            }
            return null;
        }

        private void OnPlayerInput(PlayerSession session, InputControls input)
        {
            if (_flying.ContainsKey(GetID64(session)))
            {
                CharacterMotorSimple motor = session.WorldPlayerEntity.GetComponent<CharacterMotorSimple>();
                Vector3 direction = new Vector3(0f, 0f, 0f);
                float speed = _flying[GetID64(session)];
                if (input.Forward)
                {
                    direction = input.DirectionVector * speed;
                }
                if (input.Backward)
                {
                    direction = input.DirectionVector * -speed;
                }
                motor.IsGrounded = true;
                motor.Set_currentVelocity(direction.normalized * _flying[GetID64(session)]);
            }
        }

        private string GetID64(PlayerSession session) => session.SteamId.ToString();

        private string GetLang(PlayerSession session, string key) => lang.GetMessage(key, this, GetID64(session));
    }
}