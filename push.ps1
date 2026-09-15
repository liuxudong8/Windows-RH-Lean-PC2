<#
Windows-RH-Lean-PC2 one-click push script
Run under repository root directory
#>
Write-Host "===== Check local changes =====" -ForegroundColor Cyan
$changes = git status --porcelain
if ([string]::IsNullOrWhiteSpace($changes)) {
    Write-Host "⚠️ No changes detected, exit." -ForegroundColor Yellow
    exit
}

$commitMsg = Read-Host -Prompt "Input commit message"
if ([string]::IsNullOrWhiteSpace($commitMsg)) {
    $commitMsg = "update: lean source & docs"
}

Write-Host "`n=== git add all ===" -ForegroundColor Cyan
git add .

Write-Host "`n=== git commit ===" -ForegroundColor Cyan
git commit -m "$commitMsg"

Write-Host "`n=== git push origin main ===" -ForegroundColor Cyan
git push origin main

Write-Host "`n✅ Push completed!" -ForegroundColor Green
$lastHash = git rev-parse --short HEAD
Write-Host "Commit hash: $lastHash"
Write-Host "Actions URL: https://github.com/liuxudong8/Windows-RH-Lean-PC2/actions`n"
