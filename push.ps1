<#
Windows-RH-Lean-PC2 one-click push script (全面版 2026-10-27)
Run under repository root directory
流程：① 同步外部产出（C:\proj2、chats\2026-10-16）到仓库内镜像 → ② git add/commit/push
#>

$repo = Split-Path -Parent $MyInvocation.MyCommand.Path
$today = Get-Date -Format "yyyy-MM-dd"

Write-Host "===== 1/5 Sync external artifacts into repo =====" -ForegroundColor Cyan

# 1) QRH Lean 项目源 → 仓库 QRH\<today> 快照（同日更新；历史快照保留不覆盖）
$qrhDst = Join-Path $repo "QRH\$today"
New-Item -ItemType Directory -Force -Path $qrhDst | Out-Null
Copy-Item -Path "C:\proj2\QRH\*" -Destination $qrhDst -Recurse -Force

# 2) C:\proj2 根新产出（编译证据/脚本/探针）→ 仓库根
$proj2Files = @(
  "QRH.lean","migrate_khat.py",
  "Dbg_Probe.lean","Dbg_Probe2.lean","Dbg_Probe3.lean",
  "dbg_probe.txt","dbg_probe2.txt","dbg_probe3.txt",
  "dbg_khat.txt","dbg_stage3.txt",
  "main_precise.txt","stage3_precise.txt","build_qrh_precise.txt",
  "build_main_s71.txt","build_qrh_s71.txt",
  "build_qrh_full_khat.txt","build_qrh_full_khat2.txt",
  "build_stage3.txt","build_stage3_core.txt","build_core_olean.txt"
)
foreach ($f in $proj2Files) {
    $s = Join-Path "C:\proj2" $f
    if (Test-Path -LiteralPath $s) { Copy-Item -LiteralPath $s -Destination $repo -Force }
}

# 3) d1 文档最新全目录 → 仓库 document\（robocopy /E 增量，退出码 0-7 为成功）
robocopy "C:\Users\shtcl\Doubao\chats\2026-10-16\document" (Join-Path $repo "document") /E /NFL /NDL /NJH /NJS /NP | Out-Null
if ($LASTEXITCODE -ge 8) { Write-Host "robocopy document FAILED ($LASTEXITCODE)" -ForegroundColor Red; exit 1 }

# 4) 数值件全目录 → 仓库 new-chat\
robocopy "C:\Users\shtcl\Doubao\chats\2026-10-16\new-chat" (Join-Path $repo "new-chat") /E /NFL /NDL /NJH /NJS /NP | Out-Null
if ($LASTEXITCODE -ge 8) { Write-Host "robocopy new-chat FAILED ($LASTEXITCODE)" -ForegroundColor Red; exit 1 }

# 5) C:\proj2\archive 过程快照 → 仓库 archive\
robocopy "C:\proj2\archive" (Join-Path $repo "archive") /E /NFL /NDL /NJH /NJS /NP | Out-Null
if ($LASTEXITCODE -ge 8) { Write-Host "robocopy archive FAILED ($LASTEXITCODE)" -ForegroundColor Red; exit 1 }

Write-Host "`n===== 2/5 Check local changes =====" -ForegroundColor Cyan
$changes = git status --porcelain
if ([string]::IsNullOrWhiteSpace($changes)) {
    Write-Host "No changes detected, exit." -ForegroundColor Yellow
    exit
}

$commitMsg = Read-Host -Prompt "Input commit message"
if ([string]::IsNullOrWhiteSpace($commitMsg)) {
    $commitMsg = "sync: lean source & docs & numerics $today"
}

Write-Host "`n=== 3/5 git add all ===" -ForegroundColor Cyan
git add .

Write-Host "`n=== 4/5 git commit ===" -ForegroundColor Cyan
git commit -m "$commitMsg"

Write-Host "`n=== 5/5 git push origin main ===" -ForegroundColor Cyan
git push origin main

Write-Host "`n✅ Push completed!" -ForegroundColor Green
$lastHash = git rev-parse --short HEAD
Write-Host "Commit hash: $lastHash"
Write-Host "Actions URL: https://github.com/liuxudong8/Windows-RH-Lean-PC2/actions`n"
