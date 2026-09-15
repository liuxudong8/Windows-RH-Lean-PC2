<#
Windows-RH-Lean-PC2 一键提交推送脚本
仓库根目录运行
#>
$commitMsg = Read-Host -Prompt "输入本次提交备注"
if ([string]::IsNullOrWhiteSpace($commitMsg)) {
    $commitMsg = "update: lean source & docs"
}

Write-Host "`n=== git add all ===" -ForegroundColor Cyan
git add .

Write-Host "`n=== git commit ===" -ForegroundColor Cyan
git commit -m "$commitMsg"

Write-Host "`n=== git push origin main ===" -ForegroundColor Cyan
git push origin main

Write-Host "`n✅ 推送完成！" -ForegroundColor Green
$lastHash = git rev-parse --short HEAD
Write-Host "本次提交哈希: $lastHash"
Write-Host "Actions地址: https://github.com/liuxudong8/Windows-RH-Lean-PC2/actions`n"
