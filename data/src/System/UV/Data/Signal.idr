module System.UV.Data.Signal

import Derive.Prelude

%language ElabReflection
%default total

||| Signalcodes we can react on.
public export
data SigCode : Type where
  SIGABRT : SigCode
  SIGFPE  : SigCode
  SIGHUP  : SigCode
  SIGILL  : SigCode
  SIGINT  : SigCode
  SIGQUIT : SigCode
  SIGSEGV : SigCode
  SIGTRAP : SigCode
  SIGUSR1 : SigCode
  SIGUSR2 : SigCode

%runElab derive "SigCode" [Show,Eq]

public export
sigToCode : SigCode -> Bits32
sigToCode SIGABRT = 6
sigToCode SIGFPE  = 8
sigToCode SIGHUP  = 1
sigToCode SIGILL  = 4
sigToCode SIGINT  = 2
sigToCode SIGQUIT = 3
sigToCode SIGSEGV = 11
sigToCode SIGTRAP = 5
sigToCode SIGUSR1 = 10
sigToCode SIGUSR2 = 12

public export
sigFromCode : Bits32 -> SigCode
sigFromCode 6 = SIGABRT
sigFromCode 8 = SIGFPE 
sigFromCode 1 = SIGHUP 
sigFromCode 4 = SIGILL 
sigFromCode 2 = SIGINT 
sigFromCode 3 = SIGQUIT
sigFromCode 11 = SIGSEGV
sigFromCode 5 = SIGTRAP
sigFromCode 10 = SIGUSR1
sigFromCode _ = SIGUSR2
