@echo off
set "TARGET_DIR=bv_decide_queries"
if not exist "%TARGET_DIR%" mkdir "%TARGET_DIR%"

:: 2. Create a safe timestamp (avoiding issues with spaces in morning hours like " 9:00")
set "TS=%date:~10,4%%date:~4,2%%date:~7,2%_%time:~0,2%%time:~3,2%%time:~5,2%"
set "TS=%TS: =0%"
set "TS=%TS:/=%"
set "TS=%TS::=%"
set "TS=%TS:.=%"

:: 3. Safely capture the first argument and strip any surrounding quotes
set "RAW_INPUT=%~1"

:: Log the invocation parameters for debugging if files aren't copying
echo Input received: "%RAW_INPUT%" > "%TARGET_DIR%\last_run_log.txt"

:: 4. Verify file existence using the unquoted path string
if exist "%RAW_INPUT%" (
    copy /Y "%RAW_INPUT%" "%TARGET_DIR%\query_%TS%.cnf" >nul
    echo Copy successful >> "%TARGET_DIR%\last_run_log.txt"
) else (
    echo File does not exist or path unreadable >> "%TARGET_DIR%\last_run_log.txt"
)