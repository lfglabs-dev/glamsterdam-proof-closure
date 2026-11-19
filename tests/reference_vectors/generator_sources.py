"""Pytest collection hook for the pinned generator's inferred manifests."""
import json
import os
from pathlib import Path


def pytest_collection_finish(session):
    root = Path(session.config.rootpath)
    rows = []
    for item in session.items:
        source = str(Path(item.path).relative_to(root))
        manifest = getattr(item, "get_manifest", lambda: None)()
        name = item.originalname or item.name
        if manifest is None:
            if "/test/gloas/" in source:
                rows.append({"python_only": source + "::" + name})
            continue
        if manifest.fork_name not in (None, "gloas"):
            continue
        key = "/".join([manifest.preset_name or item.callspec.params["preset"], "gloas",
                        manifest.runner_name, manifest.handler_name, manifest.suite_name, manifest.case_name])
        rows.append({"case": key, "source": source + "::" + name})
    Path(os.environ["GLOAS_SOURCE_CATALOG"]).write_text(json.dumps(rows))
