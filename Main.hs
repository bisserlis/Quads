{-# LANGUAGE BangPatterns
           , FlexibleContexts
           , RecordWildCards
           #-}

module Main where

import           Codec.Picture               hiding (Image)
import           Codec.Picture.Repa          (readImageRGBA)
import           Codec.Picture.Repa          (collapseColorChannel)
import qualified Codec.Picture.Types         as JuicyPixels

import           Data.Array.Repa             (Array, Source, D, U)
import           Data.Array.Repa             (computeP, computeS, delay)
import           Data.Array.Repa             (extent, size, extract)
import           Data.Array.Repa             (fromFunction, unsafeIndex)
import           Data.Array.Repa             (toUnboxed)
import           Data.Array.Repa.Index
import           Data.Array.Repa.Unsafe

import           Data.Vector.Unboxed         (Vector, (!), modify, ifoldl')
import qualified Data.Vector.Unboxed         as Vector
import           Data.Vector.Unboxed.Mutable (write)

import           Control.Monad               (forM_)
import           Data.Functor.Identity       (Identity(..))
import           Data.Word                   (Word8)
import           System.Environment          (getArgs)

data Quad = Quad { ul :: Quad, ule :: Error
                 , ur :: Quad, ure :: Error
                 , bl :: Quad, ble :: Error
                 , br :: Quad, bre :: Error }
          | Leaf DIM2 DIM2 Color
    deriving Show

type Image r = Array r DIM2 Color
type Histogram = (Vector Int, Vector Int, Vector Int)
type Channel = Word8
type Color = (Channel, Channel, Channel)
type Error = Double

main :: IO ()
main = do [filename] <- getArgs
          image <- loadImage filename
          let root = fst $ leaf image (Z :. 0 :. 0) (extent image)
              iterations = iterate (fst . iterateQuad image) root
          forM_ (take 1000 (zip [0..] iterations)) (\(i, q) -> writeImage ("output/" ++ show i ++ ".png") q)

loadImage :: FilePath -> IO (Image D)
loadImage filename = do eitherFile <- readImageRGBA filename
                        return $ either error collapseColorChannel eitherFile

writeImage :: FilePath -> Quad -> IO ()
writeImage filename r = writePng filename $ image
    where image = jpSaveHack (runIdentity $ computeP (renderQuad blockStyle r))

iterator a = fst . iterateQuad a

jpSaveHack :: Image U -> JuicyPixels.Image PixelRGB8
jpSaveHack a = generateImage fnElem x y
    where
          (Z :. y :. x) = extent a
          
          fnElem i j = toPixel $ a `unsafeIndex` (Z :. j :. i)
            where
                  toPixel (r, g, b) = PixelRGB8 r g b
                  {-# INLINE toPixel #-}
          {-# INLINE fnElem #-}

histogram :: Image U -> Histogram
histogram = Vector.foldl' addToHist histZero . toUnboxed
    where
          channelZero = Vector.replicate 256 0
          histZero = (channelZero, channelZero, channelZero)
          
          addToHist (!histr, !histg, !histb) (wr, wg, wb) =
              ( modify (\v -> write v r (histr ! r + 1)) histr
              , modify (\v -> write v g (histb ! g + 1)) histg
              , modify (\v -> write v b (histg ! b + 1)) histb
              )
            where (r, g, b) =
                   (fromIntegral wr, fromIntegral wg, fromIntegral wb)

weightedAverage :: Vector Int -> (Channel, Error)
weightedAverage hist | total == 0 = (0, 0) 
                     | otherwise  = (fromIntegral value, error)
    where total = Vector.sum hist
          value = ifoldl' (\a i x -> a + i * x) 0 hist `div` total
          error = sqrt (fromIntegral (ifoldl' (\a i x -> a + err i x) 0 hist)
                        / fromIntegral total)
            where err j y = y * (value - j) ^ 2

averageColor :: Histogram -> (Color, Error)
averageColor (histr, histg, histb) = ((r, g, b), e)
    where (r, re) = weightedAverage histr
          (g, ge) = weightedAverage histg
          (b, be) = weightedAverage histb
          e = re * 0.2989 + ge * 0.5870 + be * 0.1140

split :: (Source r Color) => Image r -> Quad -> (Quad, Error)
split _ Quad{} = error "Can only split leaves"
split a (Leaf (Z :. y :. x) (Z :. j :. i) _) = 
        ( Quad ull ulle url urle
               bll blle brl brle
        , maximum [ulle, urle, blle, brle] )
    where
          i' = i `div` 2
          j' = j `div` 2
          
          (ull, ulle) = leaf a (Z :. y      :. x     ) (Z :.     j' :.     i')
          (url, urle) = leaf a (Z :. y      :. x + i') (Z :.     j' :. i - i')
          (bll, blle) = leaf a (Z :. y + j' :. x     ) (Z :. j - j' :.     i')
          (brl, brle) = leaf a (Z :. y + j' :. x + i') (Z :. j - j' :. i - i')

leaf :: (Source r Color) => Image r -> DIM2 -> DIM2 -> (Quad, Error)
leaf a start dim = (Leaf start dim color, weight dim error)
    where
          (color, error) = averageColor . histogram . computeS
                         $ extract start dim a
          
          weight sh e = e * fromIntegral (size sh) ** 0.25

iterateQuad :: (Source r Color) => Image r -> Quad -> (Quad, Error)
iterateQuad a q@Quad{..} | isMax ule = let (newq, newe) = iterateQuad a ul
                                           maxe = maximum [newe, ure, ble, bre]
                                       in (q{ul = newq, ule = newe}, maxe)
                         | isMax ure = let (newq, newe) = iterateQuad a ur
                                           maxe = maximum [ule, newe, ble, bre]
                                       in (q{ur = newq, ure = newe}, maxe)
                         | isMax ble = let (newq, newe) = iterateQuad a bl
                                           maxe = maximum [ule, ure, newe, bre]
                                       in (q{bl = newq, ble = newe}, maxe)
                         | isMax bre = let (newq, newe) = iterateQuad a br
                                           maxe = maximum [ule, ure, ble, newe]
                                       in (q{br = newq, bre = newe}, maxe)
    where
          isMax e = e == maximum [ule, ure, ble, bre]
iterateQuad a l = split a l

quadpend :: (Source r Color, Source s Color, Source t Color, Source u Color)
         => Image r -> Image s -> Image t -> Image u -> Image D
quadpend a1 a2 a3 a4 = unsafeTraverse4 a1 a2 a3 a4 fnExtent fnElem
    where
          (Z :. y :. x) = extent a1
          
          fnExtent (Z :. j :. i) _ _ (Z :. j' :. i') = Z :. j + j' :. i + i'
          
          fnElem f1 f2 f3 f4 (Z :. j :. i)
            | j < y && i < x = f1 (Z :. j     :. i    )
            | j < y          = f2 (Z :. j     :. i - x)
            |          i < x = f3 (Z :. j - y :. i    )
            | otherwise      = f4 (Z :. j - y :. i - x)
{-# INLINE quadpend #-}

renderQuad :: (Source r Color) => (Quad -> Image r) -> Quad -> Image D
renderQuad style (Quad ulq _ urq _ blq _ brq _) =
        quadpend ula ura bla bra
    where
          ula = renderQuad style ulq
          ura = renderQuad style urq
          bla = renderQuad style blq
          bra = renderQuad style brq
renderQuad style l = delay $ style l
{-# INLINE renderQuad #-}

blockStyle :: Quad -> Image D
blockStyle Quad{} = error "Can't style a Quad"
blockStyle (Leaf _ sh color) = fromFunction sh (const color)
{-# INLINE blockStyle #-}

uncollapseColorChannel :: (Source r Color) => Image r -> Array D DIM3 Channel
uncollapseColorChannel a = fromFunction (extent a :. 4) fnElem
    where
          fnElem (sh :. c) | c == 0 = (\(r, _, _) -> r) (a `unsafeIndex` sh)
                           | c == 1 = (\(_, g, _) -> g) (a `unsafeIndex` sh)
                           | c == 2 = (\(_, _, b) -> b) (a `unsafeIndex` sh)
                           | otherwise = 0
          {-# INLINE fnElem #-}
{-# INLINE uncollapseColorChannel #-}
