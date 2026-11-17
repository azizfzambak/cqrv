# Builds paper/Zambak_2026_CQRV.pdf (and out/Zambak_2026_CQRV.docx) from paper/Zambak_2026_CQRV.md.
# Windows: Python with markdown-it-py, pymupdf and python-docx; Microsoft Edge (headless print).
# Run from any directory: powershell -ExecutionPolicy Bypass -File paper\tools\build.ps1
$ErrorActionPreference = "Stop"
$T = Split-Path -Parent $MyInvocation.MyCommand.Path
$P = Split-Path -Parent $T
$O = Join-Path $P "out"
New-Item -ItemType Directory -Force $O | Out-Null
$env:PYTHONIOENCODING = "utf-8"
python (Join-Path $T "build_html.py")
$edge = "C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe"
if (-not (Test-Path $edge)) { $edge = "C:\Program Files\Microsoft\Edge\Application\msedge.exe" }
$html = "file:///" + ((Join-Path $O "paper.html") -replace '\\', '/')
$raw = Join-Path $O "raw.pdf"
if (Test-Path $raw) { Remove-Item $raw -Confirm:$false }
Start-Process -FilePath $edge -Wait -ArgumentList @("--headless=new", "--disable-gpu", "--no-pdf-header-footer",
  "--print-to-pdf-no-header", "--user-data-dir=$O\edgeprof", "--print-to-pdf=$raw", $html)
Start-Sleep -Seconds 2
python (Join-Path $T "pdf_post.py")
python (Join-Path $T "build_docx.py")
