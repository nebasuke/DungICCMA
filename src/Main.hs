-- |This module implements a command-line interface to the implementation of 
-- Dung's argumentation frameworks. Dung + Haskell = Dungell
--
-- Code in this module partly taken from/inspired by Shinobu
-- See: http://zuttobenkyou.wordpress.com/2011/04/19/haskell-using-cmdargs-single-and-multi-mode/
-- and http://listx.github.com/
{-# LANGUAGE DeriveDataTypeable, RecordWildCards #-}
module Main
  (
    main
  )
 where
import Language.Dung.AF(groundedExt, preferredExt, stableExt, semiStableExt,
                        DungAF(..),
                        f, groundedF', completeF, preferredF, stableF
                        )
import Language.Dung.Input
import Language.Dung.Output

import System.Console.CmdArgs
import System.Environment (getArgs, withArgs)
import System.Exit
import Control.Monad (when, unless)
import System.IO(stderr, hPutStr, hPutStrLn)

import Data.Char(toLower, toUpper)
import Data.List(isInfixOf)

-- For the implementation of nub
import qualified Data.Set as Set

-- Haskell library's nub only require an Eq instance.
-- If we have an Ord instance as well, it can be sped up significantly.
-- I therefore use nub from https://github.com/nh2/haskell-ordnub 
-- by Niklas Hambuechen
nub :: (Ord a) => [a] -> [a]
nub = go Set.empty
  where
    go _ [] = []
    go s (x:xs) = if x `Set.member` s then go s xs
                                      else x : go (Set.insert x s) xs

data MyOptions = MyOptions {
  formats     :: Bool,
  problems    :: Bool,
  problem     :: String,
  argument    :: String,
  cegartix    :: Bool,
  laxCegartix :: Bool,
  fileName    :: String,
  fileFormat  :: String,
  outputFile  :: String,
  grounded    :: Bool,
  preferred   :: Bool,
  stable      :: Bool,
  semiStable  :: Bool,
  all         :: Bool
 } deriving (Show, Data, Typeable)

myProgOpts :: MyOptions
myProgOpts = MyOptions
    { formats     = False &= help "Prints the supported formats of the solver"
    , problems    = False &= help "Prints the supported computation problems"
    , problem     = def   &= name "p" &= help "Solve the given problem parameter"
    , argument    = def   &= name "a" &= help "Solve the problem for the given argument parameter"
    , cegartix    = True  &= help "Output in strict CEGARTIX/PrefSat format (standard)" 
    , laxCegartix = False &= help "Output in lax CEGARTIX/PrefSat format (+parentheses)" 
    , fileName    = def   &= name "f" &= typFile &= help "Name of the file to be read"
    , fileFormat  = "apx" &= name "fo" &= help "Format of the file to be read (only APX)"
    , outputFile  = def   &= typFile &= help "Name of the file to be written"
    , grounded    = False &= help "Output grounded extension for the AF"
    , preferred   = False &= help "Output preferred extensions for the AF"
    , stable      = False &= help "Output stable extensions for the AF"
    , semiStable  = False &= help "Output semi-stable extensions for the AF"
    , all         = False &= help "Output extensions of all implemented semantics for AF"
    }
 
getOpts :: IO MyOptions
getOpts = cmdArgs $ myProgOpts
    -- &= verbosityArgs [explicit, name "Verbose", name "V"] []
    &= versionArg [explicit, name "version", name "v", summary _PROGRAM_INFO]
    &= summary _PROGRAM_INFO
    &= help _PROGRAM_ABOUT
    &= helpArg [explicit, name "help", name "h"]
    &= program _PROGRAM_NAME
 
_PROGRAM_NAME = "DungellICCMA"
_PROGRAM_VERSION = "1.1"
_COPYRIGHT = "(C) Bas van Gijzel <bmv@cs.nott.ac.uk> 2014"
_PROGRAM_INFO = _PROGRAM_NAME ++ " version " ++ _PROGRAM_VERSION ++ "\n" ++ _COPYRIGHT
_PROGRAM_ABOUT = "An ICCMA-compliant implementation of Dung's AFs"


--------------------------------------------------------------------------
-- Bunch of functions to directly support printing to standard error
-- instead of standard output. 
--------------------------------------------------------------------------
putStrErr :: String -> IO ()
putStrErr = hPutStr stderr

putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

printErr :: Show a => a -> IO ()
printErr x = putStrLnErr (show x)
--------------------------------------------------------------------------

-- Removes quotes from a String
remQuote :: String -> String
remQuote = filter (/= '"')

-- This solver currently only supports ASPARTIX/CEGARTIX format. 
formatString :: String
formatString = remQuote . show $ ["apx"] -- No support for tgf

-- A string containing all the decidability problems, with all the double quotes filtered out. 
problemArgString :: String 
problemArgString = remQuote . show $
        ["DC-CO",   	-- Decide credulously according to Complete semantics
         "DC-GR",       -- Decide credulously according to Grounded semantics
         "DC-PR",       -- Decide credulously according to Preferred semantics
         "DC-ST",       -- Decide credulously according to Stable semantics
         "DS-CO",       -- Decide skeptically according to Complete semantics
         "DS-GR",       -- Decide skeptically according to Grounded semantics
         "DS-PR",       -- Decide skeptically according to Preferred semantics
         "DS-ST"]       -- Decide skeptically according to Stable semantics

-- A string containing all the enumeration problems, with all the double quotes filtered out. 
problemString :: String
problemString = remQuote . show $
        ["EE-CO",       -- Enumerate all the extensions according to Complete semantics
         "EE-GR",       -- Enumerate all the extensions according to Grounded semantics
         "EE-PR",       -- Enumerate all the extensions according to Preferred semantics
         "EE-ST",       -- Enumerate all the extensions according to Stable semantics
         "SE-CO",       -- Enumerate some extension according to Complete semantics
         "SE-GR",       -- Enumerate some extension according to Grounded semantics
         "SE-PR",       -- Enumerate some extension according to Preferred semantics
         "SE-ST"]       -- Enumerate some extension according to Stable semantics

-- Change -fo into --fo to support probo interface.
fixFormat :: [String] -> [String]
fixFormat = map (\ s -> if s == "-fo" then "--fo" else s)

-- Converts a Boolean to a String. 
boolToString :: Bool -> String
boolToString True  = "YES"
boolToString False = "NO"

-- Solve a given decidability problem, for a specific AF and argument.
solveProblemArg :: (Show arg, Eq arg, Ord arg) => String -> DungAF arg -> arg -> String
solveProblemArg "DC-CO" af a = boolToString . or . map (a `elem`) $ completeF af 
solveProblemArg "DC-GR" af a = boolToString . (a `elem`) . groundedF' $ f af 
solveProblemArg "DC-PR" af a = boolToString . or . map (a `elem`) $ preferredF af
solveProblemArg "DC-ST" af a = boolToString . or . map (a `elem`) $ stableF af
solveProblemArg "DS-CO" af a = boolToString . and . map (a `elem`) $ completeF af 
solveProblemArg "DS-GR" af a = boolToString . (a `elem`) . groundedF' $ f af 
solveProblemArg "DS-PR" af a = boolToString . and . map (a `elem`) $ preferredF af
solveProblemArg "DS-ST" af a = boolToString . and . map (a `elem`) $ stableF af
solveProblemArg s       _  _  = error $ "Input not properly processed to solveProblemArg function! Undefined problem string: " ++ s

-- Solve a given enumeration problem, for a specific AF.
solveProblem :: (Show arg, Eq arg, Ord arg) => String -> DungAF arg -> String
solveProblem "EE-CO" af = show $ completeF af
solveProblem "EE-GR" af = show . (: []) . groundedF' $ f af 
solveProblem "EE-PR" af = show $ preferredF af
solveProblem "EE-ST" af = show $ stableF af
solveProblem "SE-CO" af = show $ head $ completeF af
solveProblem "SE-GR" af = show . groundedF' $ f af 
solveProblem "SE-PR" af = show . head $ preferredF af
solveProblem "SE-ST" af = let st = stableF af
                          in if null st then "NO" else show $ head st                          
solveProblem s       _  = error $ "Input not properly processed to solveProblem function! Undefined problem string: " ++ s

main :: IO ()
main = do 
        args <- getArgs
        -- Hack to change -fo into --fo to support probo interface:
        let args' = fixFormat args
        -- Call --version with no arguments, otherwise call getOpts with the probo-supported arguments
        opts <- withArgs (if null args' then ["--version"] else args') getOpts
        optionHandler opts

-- |Check any malformed arguments/missing arguments. 
optionHandler :: MyOptions -> IO ()
optionHandler opts@MyOptions{..}  = do 
    when formats  $ putStr formatString  >> exitSuccess
    when problems $ putStr problemString >> exitSuccess
    unless (map toLower fileFormat == "apx") $ putStrLnErr "Only apx file format is supported" >> exitWith (ExitFailure 1)
    when (null fileName) $ putStrLnErr "--fileName is blank!" >> exitWith (ExitFailure 1)
    input <- readFile fileName
    let opts' = opts {cegartix = not laxCegartix, problem = map toUpper problem}
    af <- case parseAF input of 
           Left err -> putStrLnErr "Parsing error: " >> printErr err >> exitWith (ExitFailure 1)
           Right af -> return af
    let opts'' = if all 
         then 
           opts' {grounded = True, preferred = True, stable = True, semiStable = True} 
         else 
           opts'
    exec opts'' af

-- |Execute supplied options
exec :: MyOptions -> DungAF String -> IO ()
exec opts@MyOptions{..} af = do
    -- print af
    
    -- If an additional argument was used a parameter, use this to handle a decidability problem:
    unless (null argument) 
       $ if problem `isInfixOf` problemArgString
           then putStr . remQuote $ solveProblemArg problem af argument
           else if problem `isInfixOf` problemString
                  then putStrErr "Enumeration should not have an argument parameter!" >> exitWith (ExitFailure 1)
                  else putStrErr "Problem is not supported!" >> exitWith (ExitFailure 1)
    
    -- If a problem was selected, but no additional argument, then it should be an enumeration problem:
    when (null argument) $
       if problem `isInfixOf` problemString
         then putStr . remQuote $ solveProblem problem af
         else if problem `isInfixOf` problemArgString 
                then putStrErr "Decidability problem needs to have an argument parameter!" >> exitWith (ExitFailure 1)
                else putStrErr "Problem is not supported!" >> exitWith (ExitFailure 1)
    
    -- Command-line options existing before implementing probo interface:
    when grounded   $ putStr "grounded: "    >> print (groundedExt af)
    when preferred  $ putStr "preferred: "   >> print (preferredExt af)
    when stable     $ putStr "stable: "      >> print (stableExt af)
    when semiStable $ putStr "semi-stable: " >> print (semiStableExt af)
    unless (null outputFile)
      $ if cegartix 
          then writeFile outputFile (toStrictCegartix af) >> putStrLn "File outputted."
          else writeFile outputFile (toCegartix af)       >> putStrLn "File outputted."