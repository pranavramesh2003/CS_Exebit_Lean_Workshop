# CS_Exebit_Lean_Workshop

A Lean 4 workshop environment with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) support.

## Using the Codespace

### Option 1: Prebuilt Image (Recommended — Fast Start)

The default `.devcontainer/devcontainer.json` uses a prebuilt Docker image (`pranavramesh2003/sal:v4.28.0`) so the codespace starts immediately without building anything.

1. Open this repository in [GitHub Codespaces](https://github.com/features/codespaces) or in VS Code with the [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) extension.
2. When prompted, click **Reopen in Container** (VS Code) or just open a new Codespace (GitHub).
3. The prebuilt environment will load with Lean v4.28.0 and all dependencies ready.

### Option 2: Build From Scratch

If you need to customise the environment or want to build the image yourself:

1. In VS Code, open the Command Palette (`F1`) and run **Dev Containers: Open Folder in Container**.
2. When prompted to choose a configuration, select **fromscratch** (or copy `.devcontainer/fromscratch/devcontainer.json` to `.devcontainer/devcontainer.json` before opening the container).
3. The container will be built locally from `.devcontainer/fromscratch/Dockerfile`.

> **Note:** Building from scratch installs elan and downloads the Lean toolchain, which can take several minutes.
