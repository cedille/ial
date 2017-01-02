module io where

open import bool
open import char
open import list
open import string
open import unit

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixl 1 _>>=_
infixl 1 _>>_

----------------------------------------------------------------------
-- postulated operations
----------------------------------------------------------------------

postulate
  return : ∀ {A : Set} → A → IO A
  _>>=_  : ∀ {A B : Set} → IO A → (A → IO B) → IO B

{-# COMPILED return (\ _ -> return )   #-}
{-# COMPILED _>>=_  (\ _ _ -> (>>=)) #-}

postulate
  putStr : string -> IO ⊤

  -- Reads a file, which is assumed to be finite. 
  readFiniteFile : string → IO string

  writeFile : string → string → IO ⊤

  -- set output to UTF-8 for Windows
  
  initializeStdoutToUTF8 : IO ⊤

  -- set newline mode for Windows
  
  setStdoutNewlineMode : IO ⊤

  getLine : IO string

{-# IMPORT System.IO #-}

private
  data simple-list (A : Set) : Set where
    nil : simple-list A
    cons : A → simple-list A → simple-list A
  
  simple-list-to-𝕃 : ∀ {A : Set} → simple-list A → 𝕃 A
  simple-list-to-𝕃 nil = []
  simple-list-to-𝕃 (cons x xs) = x :: (simple-list-to-𝕃 xs)

{-# COMPILED_DATA simple-list ([]) [] (:) #-}

private
  postulate
    privGetArgs : IO (simple-list string)
    privDoesFileExist : string → IO 𝔹
    privCreateDirectoryIfMissing : 𝔹 → string → IO ⊤
    privTakeDirectory : string → string
    privTakeFileName : string → string
    privCombineFileNames : string → string → string
    privForceFileRead : string {- the contents of the file, not the file name -} → IO ⊤

    privGetHomeDirectory : IO string

{-# IMPORT Control.DeepSeq #-}
{-# IMPORT Data.Text.IO #-}
{-# COMPILED putStr         Data.Text.IO.putStr                #-}
{-# COMPILED readFiniteFile (\y -> let x = Data.Text.unpack y in do inh <- System.IO.openFile x System.IO.ReadMode; System.IO.hSetEncoding inh System.IO.utf8; fileAsString <- System.IO.hGetContents inh; Control.DeepSeq.rnf fileAsString `seq` System.IO.hClose inh; return (Data.Text.pack fileAsString)) #-}
{-# COMPILED writeFile (\path -> (\str -> do outh <- System.IO.openFile (Data.Text.unpack path) System.IO.WriteMode; System.IO.hSetNewlineMode outh System.IO.noNewlineTranslation; System.IO.hSetEncoding outh System.IO.utf8; Data.Text.IO.hPutStr outh str; System.IO.hFlush outh; System.IO.hClose outh; return () )) #-}
{-# COMPILED initializeStdoutToUTF8  System.IO.hSetEncoding System.IO.stdout System.IO.utf8 #-}
{-# COMPILED setStdoutNewlineMode System.IO.hSetNewlineMode System.IO.stdout System.IO.universalNewlineMode #-}
{-# IMPORT System.Environment #-}
{-# COMPILED privGetArgs (do l <- System.Environment.getArgs; return (map Data.Text.pack l)) #-}
{-# IMPORT System.Directory #-}
{-# COMPILED privForceFileRead (\ contents -> seq (length (Data.Text.unpack contents)) (return ())) #-}
{-# COMPILED privDoesFileExist (\ s -> System.Directory.doesFileExist (Data.Text.unpack s)) #-}
{-# COMPILED privCreateDirectoryIfMissing (\ b s -> System.Directory.createDirectoryIfMissing b (Data.Text.unpack s)) #-}
{-# IMPORT System.FilePath #-}
{-# COMPILED privTakeDirectory (\ s -> Data.Text.pack (System.FilePath.takeDirectory (Data.Text.unpack s))) #-}
{-# COMPILED privTakeFileName (\ s -> Data.Text.pack (System.FilePath.takeFileName (Data.Text.unpack s))) #-}
{-# COMPILED privCombineFileNames (\ s1 s2 -> Data.Text.pack (System.FilePath.combine (Data.Text.unpack s1) (Data.Text.unpack s2))) #-}
{-# COMPILED getLine (Data.Text.IO.hGetLine System.IO.stdin) #-}
{-# COMPILED privGetHomeDirectory (do x <- System.Directory.getHomeDirectory; return (Data.Text.pack x)) #-}

getArgs : IO (𝕃 string)
getArgs = privGetArgs >>= (λ args → return (simple-list-to-𝕃 args))

doesFileExist : string → IO 𝔹
doesFileExist = privDoesFileExist

createDirectoryIfMissing : 𝔹 → string → IO ⊤
createDirectoryIfMissing = privCreateDirectoryIfMissing

takeDirectory : string → string
takeDirectory = privTakeDirectory

takeFileName : string → string
takeFileName = privTakeFileName

combineFileNames : string → string → string
combineFileNames = privCombineFileNames

forceFileRead : string {- the contents of the file, not the file name -} → IO ⊤
forceFileRead = privForceFileRead

getHomeDirectory : IO string
getHomeDirectory = privGetHomeDirectory

postulate
  fileIsOlder : string → string → IO 𝔹
  canonicalizePath : string → IO string 
{-# COMPILED fileIsOlder (\ s1 s2 -> (System.Directory.getModificationTime (Data.Text.unpack s1)) >>= \ t1 -> (System.Directory.getModificationTime (Data.Text.unpack s2)) >>= \ t2 -> return (t1 < t2)) #-}
{-# COMPILED canonicalizePath (\ s -> do x <- System.Directory.canonicalizePath (Data.Text.unpack s); return (Data.Text.pack x)) #-}

----------------------------------------------------------------------
-- defined operations
----------------------------------------------------------------------

_>>_ : ∀ {A B : Set} → IO A → IO B → IO B
x >> y = x >>= (λ q -> y)

base-filenameh : 𝕃 char → 𝕃 char
base-filenameh [] = []
base-filenameh ('.' :: cs) = cs
base-filenameh (_ :: cs) = base-filenameh cs

-- return the part of the string up to the last (rightmost) period ('.'); so for "foo.txt" return "foo"
base-filename : string → string
base-filename s = 𝕃char-to-string (reverse (base-filenameh (reverse (string-to-𝕃char s))))

