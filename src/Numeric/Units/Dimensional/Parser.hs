module Numeric.Units.Dimensional.Parser
    ( -- * Parsing physical quantities
      parseQuantity
    , parseBoundedQuantity
      -- * Parsing units of measurement
    , parseUnit
    ) where

import "base" Control.Monad ( mzero )
import "base" Data.Functor ( ($>) )
import "base" Data.Functor.Identity ( Identity )
import "base" Data.List ( foldl', sortBy, intercalate )
import "base" Data.Maybe ( listToMaybe )
import "base" Data.Monoid ( (<>) )
import "base" Data.Ord ( comparing )
import "base" Data.Proxy ( Proxy(..) )
import "containers" Data.Map ( Map )
import qualified "containers" Data.Map as M
import "dimensional" Numeric.Units.Dimensional
    ( KnownDimension, Unit, Metricality(NonMetric)
    , Quantity
    , (*~)
    , dimension, mkUnitR, siUnit, one, exactValue
    , DOne, DLength, DMass, DTime, DElectricCurrent, DThermodynamicTemperature
    , DAmountOfSubstance, DLuminousIntensity
    )
import "dimensional" Numeric.Units.Dimensional.SIUnits
import "dimensional" Numeric.Units.Dimensional.NonSI
import "dimensional" Numeric.Units.Dimensional.UnitNames ( baseUnitName )
import "dimensional" Numeric.Units.Dimensional.Quantities
import qualified "dimensional" Numeric.Units.Dimensional.Dimensions.TermLevel as DimTL
import "dimensional" Numeric.Units.Dimensional.Dimensions.TermLevel ( Dimension'(..) )
import "exact-pi" Data.ExactPi ( ExactPi )
import           "parsec" Text.Parsec
import           "parsec" Text.Parsec.Error
import           "parsec" Text.Parsec.Expr
import           "parsec" Text.Parsec.Pos ( initialPos )
import qualified "parsec" Text.Parsec.Token as P
import           "parsec" Text.Parsec.Language ( emptyDef )
import "scientific" Data.Scientific ( Scientific, base10Exponent )


--------------------------------------------------------------------------------

{- |
Parses a physical quantity

The parser tries the uphold the rules and style conventions as
expressed by the NIST <#note1 [1]><#note2 [2]>, but it is more lenient.

== References

1. #note1# http://physics.nist.gov/Pubs/SP811/sec07.html
2. #note2# http://physics.nist.gov/Pubs/SP811/sec06.html
-}
parseQuantity
    :: (KnownDimension d)
    => String -- ^ Input to be parsed
    -> Either String (Quantity d ExactPi)
parseQuantity input =
    case listToMaybe $ reverse (readsPrec 0 input) of
      Nothing -> Left "can't parse Scientific value of quantity"
      Just (value, rest) -> do
        unit <- parseUnit rest
        Right $ realToFrac (value :: Scientific) *~ unit

{- |
Parses a physical quantity and guards against dangerously large inputs

See 'parseQuantity'.
-}
parseBoundedQuantity
    :: (KnownDimension d)
    => Int -- ^ Maximum allowed exponent in the value of the physical quantity
    -> String -- ^ Input to be parsed
    -> Either String (Quantity d ExactPi)
parseBoundedQuantity maxExponent input =
    case listToMaybe $ reverse (readsPrec 0 input) of
      Nothing -> Left "can't parse Scientific value of quantity"
      Just (value, rest) ->
        if base10Exponent value > maxExponent
        then Left "value is too large"
        else do
          unit <- parseUnit rest
          Right $ realToFrac value *~ unit

{- |
Parses a unit of measurement

The parser tries the uphold the rules and style conventions as
expressed by the NIST <#note1 [1]>, but it is more lenient.

== References

1. #note1# http://physics.nist.gov/Pubs/SP811/sec06.html
-}
parseUnit :: (KnownDimension d) => String -> Either String (Unit 'NonMetric d ExactPi)
parseUnit input =
    case parseUnitExp True input of
      Left  err     -> Left $ show err
      Right unitExp -> promoteUnitExp unitExp


--------------------------------------------------------------------------------
-- Unit expressions
--------------------------------------------------------------------------------

data UnitExp =
      UEName ExactPi String Dimension'
    | UEMul UnitExp UnitExp
    | UEDiv UnitExp UnitExp
    | UEPow UnitExp Int
      deriving Show

data UnitExpP =
      UEPName ExactPi String Dimension'
    | UEPInt Int
    | UEPMul UnitExpP UnitExpP
    | UEPDiv UnitExpP UnitExpP
    | UEPPow UnitExpP UnitExpP
      deriving Show

promoteUnitExp :: forall d. (KnownDimension d) => UnitExp -> Either String (Unit 'NonMetric d ExactPi)
promoteUnitExp unitExp
    | unitExpDim == dim' = Right $ mkUnitR (baseUnitName dim') value siUnit
    | otherwise = Left $ "dimension mismatch: expected " <> prettyDimension dim' <> " but got " <> prettyDimension unitExpDim
  where
    unitExpDim = unitExpDimension unitExp
    value = unitExpValue unitExp
    dim' = dimension (Proxy :: Proxy d)

unitExpDimension :: UnitExp -> Dimension'
unitExpDimension = go
  where
    go (UEName _ _ d) = d
    go (UEMul x y) = go x DimTL.* go y
    go (UEDiv x y) = go x DimTL./ go y
    go (UEPow x i) = go x DimTL.^ fromIntegral i

convertParsedExp :: UnitExpP -> Maybe UnitExp
convertParsedExp = go
  where
    go (UEPName p n dim)     = Just $ UEName p n dim
    go (UEPInt _)            = Nothing
    go (UEPMul x y)          = UEMul <$> go x <*> go y
    go (UEPDiv x y)          = UEDiv <$> go x <*> go y
    go (UEPPow x (UEPInt i)) = (`UEPow` i) <$> go x
    go (UEPPow _ _)          = Nothing

unitExpValue :: UnitExp -> ExactPi
unitExpValue (UEName px _ _) = px
unitExpValue (UEMul x y) = unitExpValue x * unitExpValue y
unitExpValue (UEDiv x y) = unitExpValue x / unitExpValue y
unitExpValue (UEPow x i) = unitExpValue x ^^ i

--------------------------------------------------------------------------------
-- Unit expression parser
--------------------------------------------------------------------------------

parseUnitExp :: Bool -> String -> Either ParseError UnitExp
parseUnitExp derived input =
    case parse (unitExpParser derived <* eof) "" input of
      Left err -> Left err
      Right uer ->
        case convertParsedExp uer of
          Just unitExp -> Right unitExp
          Nothing -> Left $ newErrorMessage (Message "Illegal expression")
                                            (initialPos "")

type UnitExpParser = Parsec String () UnitExpP

unitExpParser :: Bool -> UnitExpParser
unitExpParser derived = spaces *> (try (expParser UName) <|> expParser USymbol)
  where
    expParser :: UnitKind -> UnitExpParser
    expParser kind = buildExpressionParser table term
      where
        table :: OperatorTable String () Identity UnitExpP
        table = [ [ binOp "^" UEPPow AssocRight ]
                , [ binOp "*" UEPMul AssocLeft
                  , binOp "·" UEPMul AssocLeft
                  , binOp "/" UEPDiv AssocLeft
                  ]
                ]

        term :: UnitExpParser
        term =  (P.parens lexer $ expParser kind)
             <|> try (UEPPow <$> (unitTerm derived kind) <*> unitSuperExp)
             <|> P.lexeme lexer (unitTerm derived kind)
             <|> (UEPInt . fromInteger) <$> P.integer lexer

-- [prefix_name] unit_name | [prefix_symbol] unit_symbol
unitTerm :: Bool -> UnitKind -> UnitExpParser
unitTerm derived kind =
    -- base units with prefixes: "kilo metre", "ms"
    try (prefixedUnit $ baseUnitTable True)
    -- derived units: "coulomb", "tesla"
    <|> try (if derived then unit derivedUnitTable else mzero)
    -- base units without prefixes: "metre", "inch", "year"
    <|> unitName (baseUnitTable False) 1
  where
    unit :: UnitTable -> UnitExpParser
    unit unitTable = try (prefixedUnit unitTable) <|> unitName unitTable 1

    prefixedUnit :: UnitTable -> UnitExpParser
    prefixedUnit unitTable = P.lexeme lexer prefixTerm >>= unitName unitTable

    prefixTerm :: Parsec String () ExactPi
    prefixTerm = choice $ map (try . (\(s, x) -> string s $> x)) prefixTable

    unitName :: UnitTable -> ExactPi -> UnitExpParser
    unitName table prefix =
        (\(sym, val, dim) -> UEPName (prefix * val) sym dim) <$> choice (map tableEntryParser table)

    tableEntryParser :: (String, ExactPi, Dimension') -> Parsec String () (String, ExactPi, Dimension')
    tableEntryParser t@(unitSymbol, _val, _unitDim) = try $ string unitSymbol $> t

    prefixTable =
        case kind of
          UName   -> siPrefixNames
          USymbol -> siPrefixSymbols

    baseUnitTable :: Bool -> UnitTable
    baseUnitTable constrainPrefix = reverse $ sortBy (comparing $ \(sym,_,_) -> sym) $
        concat [ map extract $ filter p dimensionlessUnits
               , map extract $ filter p amountOfSubstanceUnits
               , map extract $ filter p timeUnits
               , map extract $ filter p lengthUnits
               , map extract $ filter p massUnits
               , map extract $ filter p electricCurrentUnits
               , map extract $ filter p thermodynamicTemperatureUnits
               , map extract $ filter p luminousIntensityUnits
               ]
      where
        p :: UnitEntry -> Bool
        p unitExp = ueKind unitExp == kind
                    && if constrainPrefix
                       then ueAllowSIPrefix unitExp
                       else True

        extract :: UnitEntry -> (String, ExactPi, Dimension')
        extract UnitEntry{..} = (ueSymbol, ueValue, ueDimension)

    derivedUnitTable :: UnitTable
    derivedUnitTable =
        map (\due -> ( dueSymbol due
                     , unitExpValue     $ dueDerivation due
                     , unitExpDimension $ dueDerivation due
                     )
            )
            derivedUnits

unitSuperExp :: UnitExpParser
unitSuperExp = UEPInt <$> P.lexeme lexer superDecimal <?> "superscript decimal"

binOp :: String -> (a -> a -> a) -> Assoc -> Operator String () Identity a
binOp name fun assoc = Infix (P.reservedOp lexer name *> pure fun) assoc

superDecimal :: (Num a) => Parsec String () a
superDecimal = superSign <*> (foldl' (\x d -> 10*x + d) 0 <$> many1 superDigit)

superDigit :: (Num a) => Parsec String () a
superDigit =
    choice
      [ 0 <$ char '⁰'
      , 1 <$ char '¹'
      , 2 <$ char '²'
      , 3 <$ char '³'
      , 4 <$ char '⁴'
      , 5 <$ char '⁵'
      , 6 <$ char '⁶'
      , 7 <$ char '⁷'
      , 8 <$ char '⁸'
      , 9 <$ char '⁹'
      ]

superSign :: (Num a) => Parsec String () (a -> a)
superSign =   (char '⁻' *> pure negate)
          <|> (char '⁺' *> pure id)
          <|> pure id

-- Lexer

unitDef :: P.LanguageDef st
unitDef = emptyDef
          { P.commentStart    = ""
          , P.commentEnd      = ""
          , P.commentLine     = ""
          , P.nestedComments  = False
          , P.identStart      = P.identLetter unitDef
          , P.identLetter     = letter
          , P.opStart         = P.opLetter unitDef
          , P.opLetter        = oneOf ['*', '·', '/', '^']
          , P.reservedNames   = []
          , P.reservedOpNames = []
          , P.caseSensitive   = True
          }

lexer :: P.GenTokenParser String u Identity
lexer = P.makeTokenParser unitDef

--------------------------------------------------------------------------------
-- SI prefixes
--------------------------------------------------------------------------------

type PrefixTable = [(String, ExactPi)]

dec :: Int -> ExactPi
dec = (10 ^^)

siPrefixNames :: PrefixTable
siPrefixNames =
  [ ("yotta", dec   24)
  , ("zetta", dec   21)
  , ("exa",   dec   18)
  , ("peta",  dec   15)
  , ("tera",  dec   12)
  , ("giga",  dec    9)
  , ("mega",  dec    6)
  , ("kilo",  dec    3)
  , ("hecto", dec    2)
  , ("deca",  dec    1)
  , ("deka",  dec    1)
  , ("deci",  dec (- 1))
  , ("centi", dec (- 2))
  , ("milli", dec (- 3))
  , ("micro", dec (- 6))
  , ("nano",  dec (- 9))
  , ("pico",  dec (-12))
  , ("femto", dec (-15))
  , ("atto",  dec (-18))
  , ("zepto", dec (-21))
  , ("yocto", dec (-24))
  ]

siPrefixSymbols :: PrefixTable
siPrefixSymbols =
  [ ("Y",  dec   24)
  , ("Z",  dec   21)
  , ("E",  dec   18)
  , ("P",  dec   15)
  , ("T",  dec   12)
  , ("G",  dec    9)
  , ("M",  dec    6)
  , ("k",  dec    3)
  , ("h",  dec    2)
  , ("da", dec    1)
  , ("d",  dec (- 1))
  , ("c",  dec (- 2))
  , ("m",  dec (- 3))
  , ("μ",  dec (- 6))
  , ("n",  dec (- 9))
  , ("p",  dec (-12))
  , ("f",  dec (-15))
  , ("a",  dec (-18))
  , ("z",  dec (-21))
  , ("y",  dec (-24))
  ]

--------------------------------------------------------------------------------
-- Unit definitions (SI & other)
--------------------------------------------------------------------------------

data UnitKind = UName | USymbol deriving (Eq, Show)
data UnitEntry =
     UnitEntry
     { ueDimension     :: Dimension'
     , ueValue         :: ExactPi
     , ueKind          :: UnitKind
     , ueSymbol        :: String
     , ueAllowSIPrefix :: Bool
     } deriving Show

data DerivedUnitEntry =
     DUE { _dueKind      :: UnitKind
         , dueSymbol     :: String
         , dueDerivation :: UnitExp
         } deriving Show

type UnitTable = [(String, ExactPi, Dimension')]


type Dummy = Double

ue :: (DimTL.HasDimension (Proxy dim)) => Unit metricality dim Dummy -> UnitKind -> String -> Bool -> UnitEntry
ue unit kind symbol allowSIPrefix =
    UnitEntry
    { ueDimension     = dimension unit
    , ueValue         = exactValue unit
    , ueKind          = kind
    , ueSymbol        = symbol
    , ueAllowSIPrefix = allowSIPrefix
    }

dimensionlessUnits :: [UnitEntry]
dimensionlessUnits =
  [ ue one         UName   "revolution"  False
  , ue one         UName   "solid"       False
  , ue degree      UName   "degree"      False
  , ue degree      USymbol "°"           False
  , ue arcminute   UName   "arcminute"   False
  , ue arcminute   USymbol "'"           False
  , ue arcsecond   UName   "arcsecond"   False
  , ue arcsecond   USymbol "\""          False
  , ue degreeOfArc UName   "degreeOfArc" False
  , ue secondOfArc UName   "secondOfArc" False
  , ue minuteOfArc UName   "minuteOfArc" False
  ]

lengthUnits :: [UnitEntry]
lengthUnits =
  [ ue metre        UName   "metre"         True
  , ue metre        USymbol "m"             True
  , ue metre        UName   "meter"         True
  , ue foot         UName   "foot"          False
  , ue inch         UName   "inch"          False
  , ue yard         UName   "yard"          False
  , ue mile         UName   "mile"          False
  , ue nauticalMile UName   "nauticalMile"  False
  , ue metre        UName   "ångström"      True
  -- , ue (prefix (dec (-10)) metre) USymbol "Å" True
  ]

massUnits :: [UnitEntry]
massUnits =
  [ ue gram      UName   "gram"       True
  , ue gram      USymbol "g"          True
  , ue poundMass UName   "poundMass"  False
  , ue tonne     UName   "tonne"      False
  , ue tonne     USymbol "T"          False
  , ue metricTon UName   "metric ton" False
  ]

timeUnits :: [UnitEntry]
timeUnits =
  [ ue second  UName   "second"  True
  , ue second  USymbol "s"       True
  , ue minute  UName   "minute"  False
  , ue minute  USymbol "min"     False
  , ue hour    UName   "hour"    False
  , ue hour    USymbol "h"       False
  , ue day     UName   "day"     False
  , ue day     USymbol "d"       False
  , ue year    UName   "year"    False
  , ue century UName   "century" False
  ]

electricCurrentUnits :: [UnitEntry]
electricCurrentUnits =
  [ ue ampere UName   "ampere" True
  , ue ampere USymbol "A"      True
  ]

thermodynamicTemperatureUnits :: [UnitEntry]
thermodynamicTemperatureUnits =
  [ ue kelvin UName   "kelvin" True
  , ue kelvin USymbol "K"      True
  ]

amountOfSubstanceUnits :: [UnitEntry]
amountOfSubstanceUnits =
  [ ue mole UName   "mole" True
  , ue mole USymbol "mol"  True
  ]

luminousIntensityUnits :: [UnitEntry]
luminousIntensityUnits =
  [ ue candela UName   "candela" True
  , ue candela USymbol "cd"      True
  ]

derivedUnits :: [DerivedUnitEntry]
derivedUnits =
    [ DUE UName "radian"    $ unsafePUE "metre / metre"
    , DUE UName "steradian" $ unsafePUE "metre² / metre²"
    , DUE UName "hertz"     $ unsafePUE "second⁻¹"
    , DUE UName "newton"    $ unsafePUE "metre · kilogram · second⁻²"
    , DUE UName "pascal"    $ unsafePUE "metre⁻¹ · kilogram · second⁻²"
    , DUE UName "joule"     $ unsafePUE "metre² · kilogram · second⁻²"
    , DUE UName "watt"      $ unsafePUE "metre² · kilogram · second⁻³"
    , DUE UName "coulomb"   $ unsafePUE "second · ampere"
    , DUE UName "volt"      $ unsafePUE "metre² · kilogram · second⁻³ · ampere⁻¹"
    , DUE UName "farad"     $ unsafePUE "metre⁻² · kilogram⁻¹ · second⁴ · ampere²"
    , DUE UName "ohm"       $ unsafePUE "metre² · kilogram · second⁻³ · ampere⁻²"
    , DUE UName "siemens"   $ unsafePUE "metre⁻² · kilogram⁻¹ · second³ · ampere²"
    , DUE UName "weber"     $ unsafePUE "metre² · kilogram · second⁻² · ampere⁻¹"
    , DUE UName "tesla"     $ unsafePUE "kilogram · second⁻² · ampere⁻¹"
    , DUE UName "henry"     $ unsafePUE "metre² · kilogram · second⁻² · ampere⁻²"
    , DUE UName "degree Celsius" $ unsafePUE "kelvin"
    , DUE UName "lumen"     $ unsafePUE "candela"
    , DUE UName "lux"       $ unsafePUE "metre² · candela"
    , DUE UName "becquerel" $ unsafePUE "second⁻¹"
    , DUE UName "gray"      $ unsafePUE "metre² · second⁻²"
    , DUE UName "sievert"   $ unsafePUE "metre² · second⁻²"
    , DUE UName "katal"     $ unsafePUE "second⁻¹ · mole"
    , DUE USymbol "rad"     $ unsafePUE "m / m"
    , DUE USymbol "sr"      $ unsafePUE "m² / m²"
    , DUE USymbol "Hz"      $ unsafePUE "s⁻¹"
    , DUE USymbol "N"       $ unsafePUE "m · kg · s⁻²"
    , DUE USymbol "Pa"      $ unsafePUE "m⁻¹ · kg · s⁻²"
    , DUE USymbol "J"       $ unsafePUE "m² · kg · s⁻²"
    , DUE USymbol "W"       $ unsafePUE "m² · kg · s⁻³"
    , DUE USymbol "C"       $ unsafePUE "s · A"
    , DUE USymbol "V"       $ unsafePUE "m² · kg · s⁻³ · A⁻¹"
    , DUE USymbol "F"       $ unsafePUE "m⁻² · kg⁻¹ · s⁴ · A²"
    , DUE USymbol "Ω"       $ unsafePUE "m² · kg · s⁻³ · A⁻²"
    , DUE USymbol "S"       $ unsafePUE "m⁻² · kg⁻¹ · s³ · A²"
    , DUE USymbol "Wb"      $ unsafePUE "m² · kg · s⁻² · A⁻¹"
    , DUE USymbol "T"       $ unsafePUE "kg · s⁻² · A⁻¹"
    , DUE USymbol "H"       $ unsafePUE "m² · kg · s⁻² · A⁻²"
    , DUE USymbol "℃"      $ unsafePUE "K"
    , DUE USymbol "°C"      $ unsafePUE "K"
    , DUE USymbol "lm"      $ unsafePUE "cd"
    , DUE USymbol "lx"      $ unsafePUE "m⁻² · cd"
    , DUE USymbol "Bq"      $ unsafePUE "s⁻¹"
    , DUE USymbol "Gy"      $ unsafePUE "m² · s⁻²"
    , DUE USymbol "Sv"      $ unsafePUE "m² · s⁻²"
    , DUE USymbol "kat"     $ unsafePUE "s⁻¹ · mol"
    ]
  where
    unsafePUE :: String -> UnitExp
    unsafePUE = either (error . show) id . (parseUnitExp False)

--------------------------------------------------------------------------------
-- Pretty printing
--------------------------------------------------------------------------------

-- | Pretty representation of a dimension.
--
-- See also: NIST Special Publication 330, 2008 Edition: The International
-- System of Units (SI), Section 1.3: Dimensions of Quantities
prettyDimension :: Dimension' -> String
prettyDimension dim =
    case M.lookup dim dimensionMap of
      Just []       -> dimFormula
      Just dimNames -> dimFormula <> " (" <> intercalate ", " dimNames <> ")"
      Nothing       -> dimFormula
  where
    dimFormula = renderDim dim

    renderDim (Dim' 0 0 0 0 0  0 0) = "dimensionless"
    renderDim (Dim' l m t i th n j) =
      concat $ filter (not . null)
                      [ f l "L"
                      , f m "M"
                      , f t "T"
                      , f i "I"
                      , f th "Θ"
                      , f n "N"
                      , f j "J"
                      ]
      where
        f :: Int -> String -> String
        f 0 _ = ""
        f e sym = sym ++ map super (show e)

        super :: Char -> Char
        super '-' = '⁻'
        super '0' = '⁰'
        super '1' = '¹'
        super '2' = '²'
        super '3' = '³'
        super '4' = '⁴'
        super '5' = '⁵'
        super '6' = '⁶'
        super '7' = '⁷'
        super '8' = '⁸'
        super '9' = '⁹'
        super c = c

dimensionMap :: Map Dimension' [String]
dimensionMap = M.fromListWith (\x y -> x <> y) $ map (\(d, n) -> (d, [n])) dimensionNames
  where
  dimensionNames :: [(Dimension', String)]
  dimensionNames =
    [ (dimension (Proxy :: Proxy DOne                           ), "dimensionless"                    )
    , (dimension (Proxy :: Proxy DLength                        ), "length"                           )
    , (dimension (Proxy :: Proxy DMass                          ), "mass"                             )
    , (dimension (Proxy :: Proxy DTime                          ), "time"                             )
    , (dimension (Proxy :: Proxy DElectricCurrent               ), "electric current"                 )
    , (dimension (Proxy :: Proxy DThermodynamicTemperature      ), "thermodynamic temperature"        )
    , (dimension (Proxy :: Proxy DAmountOfSubstance             ), "amount of substance"              )
    , (dimension (Proxy :: Proxy DLuminousIntensity             ), "luminous intensity"               )
    , (dimension (Proxy :: Proxy DArea                          ), "area"                             )
    , (dimension (Proxy :: Proxy DVolume                        ), "volume"                           )
    , (dimension (Proxy :: Proxy DVelocity                      ), "velocity"                         )
    , (dimension (Proxy :: Proxy DAcceleration                  ), "acceleration"                     )
    , (dimension (Proxy :: Proxy DWaveNumber                    ), "wave number"                      )
    , (dimension (Proxy :: Proxy DMassDensity                   ), "mass density"                     )
    , (dimension (Proxy :: Proxy DDensity                       ), "density"                          )
    , (dimension (Proxy :: Proxy DSpecificVolume                ), "specific volume"                  )
    , (dimension (Proxy :: Proxy DCurrentDensity                ), "current density"                  )
    , (dimension (Proxy :: Proxy DMagneticFieldStrength         ), "magnetic field strength"          )
    , (dimension (Proxy :: Proxy DAmountOfSubstanceConcentration), "amount of substance concentration")
    , (dimension (Proxy :: Proxy DConcentration                 ), "concentration"                    )
    , (dimension (Proxy :: Proxy DLuminance                     ), "luminance"                        )
    , (dimension (Proxy :: Proxy DPlaneAngle                    ), "planeangle"                       )
    , (dimension (Proxy :: Proxy DSolidAngle                    ), "solidangle"                       )
    , (dimension (Proxy :: Proxy DFrequency                     ), "frequency"                        )
    , (dimension (Proxy :: Proxy DForce                         ), "force"                            )
    , (dimension (Proxy :: Proxy DPressure                      ), "pressure"                         )
    , (dimension (Proxy :: Proxy DStress                        ), "stress"                           )
    , (dimension (Proxy :: Proxy DEnergy                        ), "energy"                           )
    , (dimension (Proxy :: Proxy DWork                          ), "work"                             )
    , (dimension (Proxy :: Proxy DQuantityOfHeat                ), "quantity of heat"                 )
    , (dimension (Proxy :: Proxy DPower                         ), "power"                            )
    , (dimension (Proxy :: Proxy DRadiantFlux                   ), "radiant flux"                     )
    , (dimension (Proxy :: Proxy DElectricCharge                ), "electric charge"                  )
    , (dimension (Proxy :: Proxy DQuantityOfElectricity         ), "quantity of electricity"          )
    , (dimension (Proxy :: Proxy DElectricPotential             ), "electric potential"               )
    , (dimension (Proxy :: Proxy DPotentialDifference           ), "potential difference"             )
    , (dimension (Proxy :: Proxy DElectromotiveForce            ), "electromotive force"              )
    , (dimension (Proxy :: Proxy DCapacitance                   ), "capacitance"                      )
    , (dimension (Proxy :: Proxy DElectricResistance            ), "electric resistance"              )
    , (dimension (Proxy :: Proxy DElectricConductance           ), "electric conductance"             )
    , (dimension (Proxy :: Proxy DMagneticFlux                  ), "magnetic flux"                    )
    , (dimension (Proxy :: Proxy DMagneticFluxDensity           ), "magnetic flux density"            )
    , (dimension (Proxy :: Proxy DInductance                    ), "inductance"                       )
    , (dimension (Proxy :: Proxy DLuminousFlux                  ), "luminousflux"                     )
    , (dimension (Proxy :: Proxy DIlluminance                   ), "illuminance"                      )
    , (dimension (Proxy :: Proxy DCelsiusTemperature            ), "celsius temperature"              )
    , (dimension (Proxy :: Proxy DActivity                      ), "activity"                         )
    , (dimension (Proxy :: Proxy DAbsorbedDose                  ), "absorbeddose"                     )
    , (dimension (Proxy :: Proxy DSpecificEnergy                ), "specific energy"                  )
    , (dimension (Proxy :: Proxy DKerma                         ), "kerma"                            )
    , (dimension (Proxy :: Proxy DDoseEquivalent                ), "dose equivalent"                  )
    , (dimension (Proxy :: Proxy DAmbientDoseEquivalent         ), "ambient dose equivalent"          )
    , (dimension (Proxy :: Proxy DDirectionalDoseEquivalent     ), "directional dose equivalent"      )
    , (dimension (Proxy :: Proxy DPersonalDoseEquivalent        ), "personal dose equivalent"         )
    , (dimension (Proxy :: Proxy DEquivalentDose                ), "equivalent dose"                  )
    , (dimension (Proxy :: Proxy DCatalyticActivity             ), "catalytic activity"               )
    , (dimension (Proxy :: Proxy DAngularVelocity               ), "angular velocity"                 )
    , (dimension (Proxy :: Proxy DAngularAcceleration           ), "angular acceleration"             )
    , (dimension (Proxy :: Proxy DDynamicViscosity              ), "dynamic viscosity"                )
    , (dimension (Proxy :: Proxy DMomentOfForce                 ), "moment of force"                  )
    , (dimension (Proxy :: Proxy DSurfaceTension                ), "surface tension"                  )
    , (dimension (Proxy :: Proxy DHeatFluxDensity               ), "heat flux density"                )
    , (dimension (Proxy :: Proxy DIrradiance                    ), "irradiance"                       )
    , (dimension (Proxy :: Proxy DRadiantIntensity              ), "radiant intensity"                )
    , (dimension (Proxy :: Proxy DRadiance                      ), "radiance"                         )
    , (dimension (Proxy :: Proxy DHeatCapacity                  ), "heat capacity"                    )
    , (dimension (Proxy :: Proxy DEntropy                       ), "entropy"                          )
    , (dimension (Proxy :: Proxy DSpecificHeatCapacity          ), "specific heat capacity"           )
    , (dimension (Proxy :: Proxy DSpecificEntropy               ), "specific entropy"                 )
    , (dimension (Proxy :: Proxy DThermalConductivity           ), "thermal conductivity"             )
    , (dimension (Proxy :: Proxy DEnergyDensity                 ), "energy density"                   )
    , (dimension (Proxy :: Proxy DElectricFieldStrength         ), "electric field strength"          )
    , (dimension (Proxy :: Proxy DElectricChargeDensity         ), "electric charge density"          )
    , (dimension (Proxy :: Proxy DElectricFluxDensity           ), "electric flux density"            )
    , (dimension (Proxy :: Proxy DPermittivity                  ), "permittivity"                     )
    , (dimension (Proxy :: Proxy DPermeability                  ), "permeability"                     )
    , (dimension (Proxy :: Proxy DMolarEnergy                   ), "molar energy"                     )
    , (dimension (Proxy :: Proxy DMolarEntropy                  ), "molar entropy"                    )
    , (dimension (Proxy :: Proxy DMolarHeatCapacity             ), "molar heat capacity"              )
    , (dimension (Proxy :: Proxy DExposure                      ), "exposure"                         )
    , (dimension (Proxy :: Proxy DAbsorbedDoseRate              ), "absorbed dose rate"               )
    , (dimension (Proxy :: Proxy DImpulse                       ), "impulse"                          )
    , (dimension (Proxy :: Proxy DMomentum                      ), "momentum"                         )
    , (dimension (Proxy :: Proxy DMassFlow                      ), "massflow"                         )
    , (dimension (Proxy :: Proxy DVolumeFlow                    ), "volume flow"                      )
    , (dimension (Proxy :: Proxy DGravitationalParameter        ), "gravitational parameter"          )
    , (dimension (Proxy :: Proxy DKinematicViscosity            ), "kinematic viscosity"              )
    , (dimension (Proxy :: Proxy DFirstMassMoment               ), "first mass moment"                )
    , (dimension (Proxy :: Proxy DMomentOfInertia               ), "moment of inertia"                )
    , (dimension (Proxy :: Proxy DAngularMomentum               ), "angular momentum"                 )
    , (dimension (Proxy :: Proxy DThermalResistivity            ), "thermal resistivity"              )
    , (dimension (Proxy :: Proxy DThermalConductance            ), "thermal conductance"              )
    , (dimension (Proxy :: Proxy DThermalResistance             ), "thermal resistance"               )
    , (dimension (Proxy :: Proxy DHeatTransferCoefficient       ), "heat transfer coefficient"        )
    , (dimension (Proxy :: Proxy DThermalAdmittance             ), "thermal admittance"               )
    , (dimension (Proxy :: Proxy DThermalInsulance              ), "thermal insulance"                )
    , (dimension (Proxy :: Proxy DJerk                          ), "jerk"                             )
    , (dimension (Proxy :: Proxy DAngle                         ), "angle"                            )
    , (dimension (Proxy :: Proxy DThrust                        ), "thrust"                           )
    , (dimension (Proxy :: Proxy DTorque                        ), "torque"                           )
    , (dimension (Proxy :: Proxy DEnergyPerUnitMass             ), "energy per unit mass"             )
    ]
