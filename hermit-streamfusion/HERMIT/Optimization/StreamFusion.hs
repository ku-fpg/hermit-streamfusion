{-# LANGUAGE OverloadedStrings #-}
module HERMIT.Optimization.StreamFusion (plugin, inlineConstructors) where

import Control.Arrow
import Control.Monad

import Data.List (partition)

import HERMIT.External
import HERMIT.GHC
import HERMIT.Kernel
import HERMIT.Kure hiding (apply)
import HERMIT.Name
import HERMIT.Plugin
import HERMIT.Plugin.Builder

import HERMIT.Dictionary

import Prelude hiding (until)

plugin :: Plugin
plugin = hermitPlugin $ \ opts -> do
    let (os,cos') = partition (`elem` ["interactive","inline","rules","showrule"]) opts
        srFlag = "showrule" `elem` os

    -- debug output phase name
    left' <- liftM passesLeft getPassInfo
    when (notNull left') $ liftIO $ putStrLn $ "=========== " ++ show left' ++ " ==========="

    pass 0 $ do
        query (Always "inject-dependency \"HERMIT.Optimization.StreamFusion.List\"")
            (promoteModGutsT (injectDependencyT $ mkModuleName "HERMIT.Optimization.StreamFusion.List") :: TransformH LCore ())
        when ("interactive" `elem` os) $ interactive sfexts cos'
        -- We need to run the rules which match on standard list combinators
        -- before the simplifier tries to use the rules that belong to them.
        when ("rules" `elem` os) $
            apply (Always "-- apply all rules") $ do
                f <- compileRulesT $ filter (`notElem` ["consS", "nilS", "singletonS"]) allRules
                tryR (repeatR (anytdR (promoteExprR $ unfoldNameR "." <+ (showRule srFlag $ runFoldR f)) <+ simplifyR))

    liftIO $ putStrLn "starting"
    apply (Always "-- concatmap -> flatten")
        $ tryR
        $ repeatR
        $ anyCallR
        $ promoteExprR
--        $ bracketR "concatmap -> flatten"
        $ concatMapSR
    liftIO $ putStrLn "ending"
    when ("inline" `elem` os) $ before SpecConstr $ apply (Always "-- inline constructors") $ tryR $ inlineConstructors
    when ("interactive" `elem` os) $ lastPass $ interactive sfexts cos'

showRule :: Bool -> RewriteH CoreExpr -> RewriteH CoreExpr
showRule True = bracketR "rule"
showRule False = (>>> traceR "rule")

inlineConstructors :: RewriteH Core
inlineConstructors = anytdR $ promoteExprR $ letT (nonRecT successT nonRecTypeDCT const) successT const >> letNonRecSubstR
    where nonRecTypeDCT = do
            (dc,_tys,_args) <- callDataConT
            guardMsg (not $ any (`eqType` dataConOrigResTy dc) (dataConOrigArgTys dc)) "constructor is recursive"

allRules :: [RuleName]
allRules =
    [ "concat/concatMap" -- important this is first
    , "concat/concatMapS" -- ditto
    , "stream/unstream"
    , "unstream/stream"
    , "allS"
    , "andS"
    , "anyS"
    , "appendS"
    , "concatMapS"
    , "concatS"
    , "consS"
    , "dropS"
    , "elemS"
    , "enumFromToS"
    , "filterS"
    , "foldlS"
    , "foldlS'"
    , "foldrS"
    , "headS"
    , "indexS"
    , "intersperseS"
    , "iterateS"
    , "lengthS"
    , "mapS"
    , "nilS"
    , "nubS"
    , "nullS"
    , "orS"
    , "singletonS"
    , "snocS"
    , "sum"
    , "tailS"
    , "takeS"
    , "unfoldrS"
    , "zipS"
    , "zipWithS"
    ]

-- All the rules with 'stream' at the head.
streamRules :: [RuleName]
streamRules = [ "stream/unstream", "consS", "nilS" ]

sfexts :: [External]
sfexts =
    [ external "concatmap" (promoteExprR concatMapSR :: RewriteH LCore)
        [ "special rule for concatmap" ]
    , external "all-rules" ((compileRulesT allRules >>= repeatR . onetdR . promoteExprR . bracketR "rule" . runFoldR) :: RewriteH LCore)
        [ "apply all the concatMap rules" ]
    , external "simp-step" (compileRulesT allRules >>= simpStep :: RewriteH LCore)
        [ "do one step of simplification" ]
    ]

concatMapSR :: RewriteH CoreExpr
concatMapSR = do
    -- concatMapS :: forall a b. (a -> Stream b) -> Stream a -> Stream b
    (_, [aTy, bTy, f]) <- callNameT "HERMIT.Optimization.StreamFusion.List.concatMapS"

    (v, n', st'') <- return f >>> ensureLam >>> exposeInnerStreamT
    st <- return st'' >>> tryR (extractR sfSimp)
    n@(Lam s _) <- return n' >>> tryR (extractR sfSimp) >>> ensureLam

    flattenSid <- findIdT "HERMIT.Optimization.StreamFusion.List.flattenS"
    fixStepid <- findIdT "HERMIT.Optimization.StreamFusion.List.fixStep"

    let st' = mkCoreTup [varToCoreExpr v, st]
    stId <- constT $ newIdH "st" (exprType st')
    wild <- constT $ cloneVarH ("wild_"++) stId

        -- fixStep :: forall a b s. a -> Step b s -> Step b (a,s)
    let fixApp = mkCoreApps (varToCoreExpr fixStepid)
                            [ aTy, bTy, Type (exprType st)
                            , varToCoreExpr v, mkCoreApp n (varToCoreExpr s) ]
        nFn = mkCoreLams [stId] $
                mkSmallTupleCase [v,s] fixApp wild (varToCoreExpr stId)
        mkFn = mkCoreLams [v] st'

    -- flattenS :: forall a b s. (a -> s) -> (s -> Step b s) -> Stream a -> Stream b
    return $ mkCoreApps (varToCoreExpr flattenSid)
                        [ aTy, bTy, Type (exprType st'), mkFn, nFn ]

-- | Getting the inner stream.
exposeInnerStreamT
    :: TransformH CoreExpr ( Var        -- the 'x' in 'concatMap (\x -> ...) ...'
                           , CoreExpr   -- inner stream stepper function
                           , CoreExpr ) -- inner stream state
exposeInnerStreamT = lamT idR getDataConInfo $ \ v [_sTy, g, st] -> (v, g, st)

ensureLam :: RewriteH CoreExpr
ensureLam = tryR (extractR simplifyR) >>> (lamAllR idR idR <+ etaExpandR "x")

-- | Return list of arguments to Stream (existential, generator, state)
getDataConInfo :: TransformH CoreExpr [CoreExpr]
getDataConInfo = go <+ (tryR (caseFloatArgR Nothing Nothing >>> (compileRulesT streamRules >>= extractR . anyCallR . promoteR . runFoldR)) >>> (compileRulesT allRules >>= extractR . simpStep) >>> getDataConInfo)
    where go = do (_dc, _tys, args) <- callDataConNameT "Stream"
                  return args

sfSimp :: RewriteH LCore
sfSimp = compileRulesT allRules >>= repeatR . simpStep

-- TODO: don't unfold recursive functions
simpStep :: CompiledFold -> RewriteH LCore
simpStep f =    simplifyR
             <+ onetdR (promoteExprR $ runFoldR f)
             <+ (onetdR (promoteExprR (   letFloatInR
                                       <+ caseElimR
                                       <+ elimExistentials
                                       <+ (caseFloatInR >>> appAllR idR idR))))
             <+ promoteExprR unfoldR -- last resort, as we don't want to unfold 'stream' before the rule can fire
             <+ fail "simpStep failed"

elimExistentials :: RewriteH CoreExpr
elimExistentials = do
    Case _s _bnd _ty alts <- idR
    guardMsg (notNull [ v | (_,vs,_) <- alts, v <- vs, isTyVar v ])
             "no existential types in patterns"
    caseAllR (extractR sfSimp) idR idR (const idR) >>> {- observeR "before reduce" >>> -} caseReduceR False -- >>> observeR "result"

