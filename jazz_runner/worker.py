import os, sys, json, asyncio, traceback, time

from cryptography.fernet import Fernet
from pyrogram import Client

import bot_core as core


async def main():
    payload = json.loads(
        Fernet(os.environ["JOB_KEY"].strip().encode())
        .decrypt(os.environ["JOB_PAYLOAD"].strip().encode())
    )
    user_id = int(payload["user_id"])
    job_id = payload["job_id"]
    cookies, key = payload["cookies"], payload["key"]
    is_batch = bool(payload.get("is_batch"))
    batch_name = payload.get("batch_name") or "Uploads"

    # Telegram progress jaldi refresh ho + Actions log me bhi live % dikhe
    core.MultiProgressTracker.UI_INTERVAL = 4.0
    _orig_render = core.MultiProgressTracker._render_ui
    _last_log = {"t": 0.0}

    async def _render_and_log(self, force=False):
        now = time.time()
        if force or now - _last_log["t"] >= 3.0:
            _last_log["t"] = now
            for tid, t in self.tasks.items():
                act = t.get("action", "")
                if act in ("Downloading", "Uploading"):
                    dl = act == "Downloading"
                    cur = t["dl_current"] if dl else t["ul_current"]
                    spd = t["dl_speed"] if dl else t["ul_speed"]
                    tot = t.get("size", 0)
                    pct = (cur / tot * 100) if tot else 0
                    print(f"[{tid}] {t['name'][:40]} | {'DL' if dl else 'UL'} {pct:5.1f}% | {core.format_bytes(cur)}/{core.format_bytes(tot)} | {core.format_bytes(spd)}/s", flush=True)
                elif act == "Uploading Part":
                    pct = (t["part_cur"] / t["part_size"] * 100) if t["part_size"] else 0
                    print(f"[{tid}] {t['name'][:40]} | UL part {t['part_i']}/{t['part_n']} {pct:5.1f}%", flush=True)
                elif force:
                    print(f"[{tid}] {t['name'][:40]} | {act}", flush=True)
        return await _orig_render(self, force)
    core.MultiProgressTracker._render_ui = _render_and_log

    conc = max(1, int(payload.get("conc", 3)))
    core.bot_settings["owner_concurrent"] = conc
    core.bot_settings["user_concurrent"] = conc
    core.bot_settings["storage_guard"] = False

    client = Client(
        "runner",
        api_id=int(os.environ["API_ID"]),
        api_hash=os.environ["API_HASH"],
        bot_token=os.environ["BOT_TOKEN"],
        in_memory=True,
    )
    await client.start()
    status_msg = None
    failed = False
    try:
        sid = payload.get("status_msg_id")
        if sid:
            m = await client.get_messages(user_id, int(sid))
            status_msg = None if (m is None or getattr(m, "empty", False)) else m

        raw = payload.get("items", [])
        ids = [int(i["msg_id"]) for i in raw if "msg_id" in i]
        msgs = {}
        if ids:
            for m in await client.get_messages(user_id, ids):
                if m and not getattr(m, "empty", False):
                    msgs[m.id] = m

        items = []
        for it in raw:
            if "url" in it:
                items.append({"url": it["url"], "filename": it["filename"]})
            else:
                m = msgs.get(int(it["msg_id"]))
                if m and m.media:
                    items.append({"msg": m, "filename": it["filename"]})

        if not items:
            raise RuntimeError("no valid files found for this job")

        loop = asyncio.get_event_loop()
        target = payload["parent_id"]
        new_folder = bool(payload.get("new_folder", is_batch))
        if new_folder:
            target = await loop.run_in_executor(
                None, core.create_cloud_folder, batch_name, payload["parent_id"], cookies, key
            )

        await core.run_pipeline(
            client, user_id, job_id, items, target, is_batch, batch_name, cookies, key,
            status_msg=status_msg, dest_path=payload.get("dest_path", "/"), new_folder=new_folder,
        )
    except Exception as e:
        failed = True
        traceback.print_exc()
        txt = f"❌ GitHub runner error — {str(e)[:300]}"
        try:
            if status_msg:
                await status_msg.edit_text(txt)
            else:
                await client.send_message(user_id, txt)
        except Exception:
            pass
    finally:
        try:
            await client.stop()
        except Exception:
            pass
    return 1 if failed else 0


if __name__ == "__main__":
    code = asyncio.get_event_loop().run_until_complete(main())
    sys.stdout.flush()
    os._exit(code)
