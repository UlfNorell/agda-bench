{-# LANGUAGE FlexibleContexts #-}

module Main where

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import Criterion.Main
import Data.List
import qualified Data.HashMap.Strict as HMap
import System.Console.GetOpt
import System.Environment

import Agda.Main (runAgda)
import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps
import qualified Agda.Interaction.Options as O
import Agda.TypeChecking.Monad as O
  -- NB: In Agda-2.6.2, commandLineOptions has moved
  -- from Agda.TypeChecking.Monad to Agda.Interaction.Options.
  -- Importing module as O is a hack to cover both
  -- 2.6.2 and previous versions of Agda without #if.
import Agda.TypeChecking.Pretty
import Agda.Syntax.Internal hiding (sort, set)
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.TheTypeChecker
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.Reduce

import Agda.Utils.Lens
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.FileName

data Options = Options { criterionOptions :: [String]
                       , singleRun        :: Maybe String
                       , customBench      :: [String]
                       , typeCheckBench   :: [(String, String)]
                       , useCallByName    :: Bool
                       , fullNormalForm   :: Bool }

defaultOptions :: Options
defaultOptions = Options [] Nothing [] [] False False

moreOpts :: Monad m => String -> Options -> m Options
moreOpts s opts = return opts{ criterionOptions = criterionOptions opts ++ words s }

setSingleRun :: Monad m => String -> Options -> m Options
setSingleRun s opts = return opts{ singleRun = Just s }

addCustomBench :: Monad m => String -> Options -> m Options
addCustomBench s opts = return opts{ customBench = customBench opts ++ [s] }

normaliseFlag :: Monad m => Options -> m Options
normaliseFlag opts = return opts{ fullNormalForm = True }

callByNameFlag :: Monad m => Options -> m Options
callByNameFlag opts = return opts{ useCallByName = True }

typeCheckFlag :: MonadError String m => String -> Options -> m Options
typeCheckFlag s opts =
  case break (== ":") (words s) of
    (e, ":" : t) -> return opts{ typeCheckBench = (unwords e, unwords t) : typeCheckBench opts }
    _ -> throwError "Usage: --type-check \"EXPR : TYPE\""

benchBackend :: Backend' Options () () () ()
benchBackend = Backend'
  { backendName           = "benchmark"
  , backendVersion        = Just "1.0.0"
  , options               = defaultOptions
  , commandLineFlags      = [ Option ['B'] ["bench-options"] (ReqArg moreOpts "ARGS")
                                "Benchmarking options. Use -B --help for more information."
                            , Option ['s'] ["single"] (ReqArg setSingleRun "EXPR")
                                "Evaluate a single expression"
                            , Option ['C'] ["custom"] (ReqArg addCustomBench "EXPR")
                                "Add a custom benchmark for EXPR"
                            , Option ['T'] ["type-check"] (ReqArg typeCheckFlag "EXPR : TYPE")
                                "Add a custom benchmark to type check EXPR against TYPE"
                            , Option ['n'] ["nf"] (NoArg normaliseFlag)
                                "Full normalisation instead of weak-head reduction"
                            , Option [] ["call-by-name"] (NoArg callByNameFlag)
                                "Use call-by-name"
                            ]
  , isEnabled             = \ _ -> True
  , preCompile            = runBenchmarks
  , postCompile           = \ _ _ _ -> return ()
  , preModule             = \ _ _ _ _ -> return (Skip ())
  , postModule            = \ _ _ _ _ _ -> return ()
  , compileDef            = \ _ _ _ _ -> return ()
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  }

findBenchmarks :: TCM [String]
findBenchmarks = do
  defs <- sort . HMap.keys . _sigDefinitions . iSignature <$> curIF
  return $ filter ("bench" `isPrefixOf`) $ map strName defs
  where
    strName = prettyShow . nameConcrete . qnameName

normaliser :: Options -> Term -> TCM Term
normaliser opts | fullNormalForm opts = strat . normalise
                | otherwise           = strat . reduce
  where
    strat | useCallByName opts = callByName
          | otherwise          = id

runBenchmarks :: Options -> TCM ()
runBenchmarks opts@Options{ singleRun = Just s } = printExpr opts 0 s
runBenchmarks opts@Options{ typeCheckBench = bs @ (_ : _) } =
  runTypeCheckBenchmarks opts bs
runBenchmarks opts = do
  benchmarks <- (++ customBench opts) <$> findBenchmarks
  actions    <- mapM (normaliseExpr $ normaliser opts) benchmarks
  let mkBench name action = bench name (whnfIO action)
      args = criterionOptions opts ++ customBench opts
  when (null args) $ do
    reportSLn "" 1 "Benchmarks:"
    verboseS "" 1 $ do
      mapM_ (printExpr opts 2) benchmarks
      reportSLn "" 1 ""
  liftIO $ withArgs args $ defaultMainWith defaultConfig $ zipWith mkBench benchmarks actions

runTypeCheckBenchmarks :: Options -> [(String, String)] -> TCM ()
runTypeCheckBenchmarks opts benchmarks = do
  let mkBench (e, t) action = bench (e ++ " : " ++ t) (whnfIO action)
      args = criterionOptions opts
  actions <- mapM typeCheckExpr benchmarks
  liftIO $ withArgs args $ defaultMainWith defaultConfig $ zipWith mkBench benchmarks actions

typeCheckExpr :: (String, String) -> TCM (IO ())
typeCheckExpr (e, t) = do
  e <- concreteToAbstract_ =<< parseExpr noRange e
  t <- isType_ =<< concreteToAbstract_ =<< parseExpr noRange t
  withCurrentFile $ tcmToIO $ do
    v <- checkExpr e t
    seq v $ return ()

tcmToIO :: TCM a -> TCM (IO a)
tcmToIO m = TCM $ \ s e -> return (unTCM m s e)

-- | Set 'envCurrentPath' to 'optInputFile'.
withCurrentFile :: TCM a -> TCM a
withCurrentFile cont = do
  mpath <- getInputFile_
  localTC (\ e -> e { envCurrentPath = mpath }) cont

-- N.B.: Just getInputFile clashes with
-- Agda.TypeChecking.Monad.getInputFile of Agda-2.6.1.
-- | Return the 'optInputFile' as 'AbsolutePath', if any.
getInputFile_ :: TCM (Maybe AbsolutePath)
getInputFile_ = mapM (liftIO . absolute) =<< do
  O.optInputFile <$> O.commandLineOptions

printExpr :: Options -> Int -> String -> TCM ()
printExpr opts n s = atTopLevel $ do
  e <- concreteToAbstract_ =<< parseExpr noRange s
  v <- fst <$> inferExpr e
  v <- normaliser opts v
  reportSDoc "" 1 $ text (replicate n ' ' ++ s ++ " =") <+> prettyTCM v

normaliseExpr :: (Term -> TCM Term) -> String -> TCM (IO ())
normaliseExpr norm s = atTopLevel $ do
  e <- concreteToAbstract_ =<< parseExpr noRange s
  v <- instantiateFull =<< fst <$> inferExpr e
  tcmToIO $ do
    v <- norm v
    seq v $ return ()

main = runAgda [Backend benchBackend]
