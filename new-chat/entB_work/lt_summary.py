# -*- coding: utf-8 -*-
import json
from collections import Counter
import numpy as np

d = json.load(open(r"C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat\entB_work\entB_lt_full.json", encoding="utf-8"))
s = d["summary"]; items = d["items"]
print("summary:", json.dumps(s, ensure_ascii=False))
print("mode:", dict(Counter(r["mode"] for r in items)))
fake = [r for r in items if r["mode"] == "fake"]
print("fake:", json.dumps(fake, ensure_ascii=False))
off = [r for r in items if r["mode"] in ("offline_shallow", "offline_pair")]
print("offline-ish:", json.dumps(off, ensure_ascii=False))
scanned = [r for r in items if r["mode"] != "online"]
print("scanned count:", len(scanned))
mh = np.array([r["mhalf"] for r in items if r["mode"] == "online"])
print("online mhalf: min %.3e med %.3e max %.3e; >1e-3: %d, >1e-4: %d"
      % (mh.min(), np.median(mh), mh.max(), int((mh > 1e-3).sum()), int((mh > 1e-4).sum())))
L_items = [r for r in items if r["fam"] == "L"]
print("L items:", json.dumps(L_items, ensure_ascii=False))
# 左尾 ĥ<1 的 46 个
lt1 = [r for r in items if r["lt1"]]
print("lt1 count:", len(lt1), "mode:", dict(Counter(r["mode"] for r in lt1)),
      "families:", dict(Counter(r["fam"] for r in lt1)))
# nn 最近邻分布
nn = np.array([r["nn"] for r in items])
print("nn: min %.4f med %.4f max %.4f" % (nn.min(), np.median(nn), nn.max()))
# 假根候选细节
print("all scanned smin/mmin:", [(r["gamma"], r["fam"], r["smin"], r["mmin"], r["mhalf"], r["mode"]) for r in scanned])
