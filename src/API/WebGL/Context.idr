--    Copyright 2017, the blau.io contributors
--
--    Licensed under the Apache License, Version 2.0 (the "License");
--    you may not use this file except in compliance with the License.
--    You may obtain a copy of the License at
--
--        http://www.apache.org/licenses/LICENSE-2.0
--
--    Unless required by applicable law or agreed to in writing, software
--    distributed under the License is distributed on an "AS IS" BASIS,
--    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
--    See the License for the specific language governing permissions and
--    limitations under the License.

module API.WebGL.Context

import API.WebGL.Buffer
import API.WebGL.Shader
import API.WebGL.Program
import IdrisScript
import IdrisScript.Arrays

%access public export
%default total

||| The WebGLRenderingContext represents the API allowing OpenGL ES 2.0 style
||| rendering into the canvas element.
|||
||| The original specification can be found at
||| https://www.khronos.org/registry/webgl/specs/latest/1.0/#WebGLRenderingContextBase
record WebGLRenderingContextBase where
  constructor New
  ||| A reference to the canvas element which created this context.
  canvas              : Ptr
  ||| The actual width of the drawing buffer. May be different from the width
  ||| attribute of the HTMLCanvasElement if the implementation is unable to
  ||| satisfy the requested widthor height.
  drawingBufferWidth  : Int
  ||| The actual height of the drawing buffer. May be different from the height
  ||| attribute of the HTMLCanvasElement if the implementation is unable to
  ||| satisfy the requested width or height.
  drawingBufferHeight : Int
  ||| A non standard field for easier JS integration
  self                : Ptr

-- ClearBufferMask
COLOR_BUFFER_BIT   : Int
COLOR_BUFFER_BIT   = 0x00004000

DEPTH_BUFFER_BIT   : Int
DEPTH_BUFFER_BIT   = 0x00000100

STENCIL_BUFFER_BIT : Int
STENCIL_BUFFER_BIT = 0x00000400

-- Begin Mode
TRIANGLES : Int
TRIANGLES = 0x0004

attachShader : WebGLRenderingContextBase -> (program : WebGLProgram) ->
               (shader : WebGLShader) -> JS_IO ()
attachShader ctx (New programRef) (New shaderRef) =
  jscall "%0.attachShader(%1, %2)" (JSRef -> JSRef -> JSRef -> JS_IO ())
  (self ctx) programRef shaderRef

bindBuffer : WebGLRenderingContextBase -> (target : Int) ->
             (buffer : WebGLBuffer) -> JS_IO ()
bindBuffer ctx target (New ref) = jscall "%0.bindBuffer(%1, %2)"
  (JSRef -> Int -> JSRef -> JS_IO ()) (self ctx) target ref

-- TODO: proper types for all arguments
bufferData : WebGLRenderingContextBase -> (target : Int) ->
             (srcData : List Double) -> (usage : Int) -> JS_IO ()
bufferData ctx target srcData usage = jscall "%0.bufferData(%1, %2, %3)"
  (JSRef -> Int -> JSRef -> Int -> JS_IO ())
  (API.WebGL.Context.WebGLRenderingContextBase.self ctx)
  target (IdrisScript.unpack !(toJSArray {to=JSNumber} srcData)) usage

compileShader : WebGLRenderingContextBase -> (shader : WebGLShader) -> JS_IO ()
compileShader ctx (New ref) =
  jscall "%0.compileShader(%1)" (JSRef -> JSRef -> JS_IO ()) (self ctx) ref

||| clears a buffer
-- TODO: Proper type for buffer
clear : WebGLRenderingContextBase -> (buffer : Int) -> JS_IO ()
clear ctx = jscall "%0.clear(%1)" (JSRef -> Int -> JS_IO ()) $ self ctx

||| clearColor sets the clear value of the color buffer.
-- TODO: Proper Type for red, green, blue, alpha
clearColor : WebGLRenderingContextBase -> (red : Double) -> (green : Double) ->
             (blue : Double) -> (alpha : Double) -> JS_IO ()
clearColor ctx = jscall "%0.clearColor(%1, %2, %3, %4)"
  (JSRef -> Double -> Double -> Double -> Double -> JS_IO ()) $ self ctx

createBuffer : WebGLRenderingContextBase -> JS_IO WebGLBuffer
createBuffer ctx = map API.WebGL.Buffer.New bufferRef where
  bufferRef : JS_IO JSRef
  bufferRef = jscall "%0.createBuffer()" (JSRef -> JS_IO JSRef) $
              API.WebGL.Context.WebGLRenderingContextBase.self ctx

createProgram : WebGLRenderingContextBase -> JS_IO WebGLProgram
createProgram ctx = map API.WebGL.Program.New programRef where
  programRef : JS_IO JSRef
  programRef = jscall "%0.createProgram()" (JSRef -> JS_IO JSRef) $
               API.WebGL.Context.WebGLRenderingContextBase.self ctx

createShader : WebGLRenderingContextBase -> (type : Int) -> JS_IO WebGLShader
createShader ctx type = map API.WebGL.Shader.New shaderRef where
  shaderRef : JS_IO JSRef
  shaderRef = jscall "%0.createShader(%1)" (JSRef -> Int -> JS_IO JSRef)
              (API.WebGL.Context.WebGLRenderingContextBase.self ctx) type

drawArrays : WebGLRenderingContextBase -> (mode : Int) -> (first : Int) ->
             (count : Int) -> JS_IO ()
drawArrays ctx = jscall "%0.drawArrays(%1, %2, %3)"
  (JSRef -> Int -> Int -> Int -> JS_IO ()) $ self ctx

linkProgram : WebGLRenderingContextBase -> (program : WebGLProgram) -> JS_IO ()
linkProgram ctx (New ref) =
  jscall "%0.linkProgram(%1)" (JSRef -> JSRef -> JS_IO ()) (self ctx) ref

useProgram : WebGLRenderingContextBase -> (program : WebGLProgram) -> JS_IO ()
useProgram ctx (New ref) =
  jscall "%0.useProgram(%1)" (JSRef -> JSRef -> JS_IO ()) (self ctx) ref

shaderSource : WebGLRenderingContextBase -> (shader : WebGLShader) ->
               (source : String) -> JS_IO ()
shaderSource ctx (New ref) =
  jscall "%0.shaderSource(%1, %2)" (JSRef -> JSRef -> String -> JS_IO ())
  (self ctx) ref

WebGLRenderingContext : Type
WebGLRenderingContext = WebGLRenderingContextBase

||| webGlRenderingContextFromPointer is a helper function for easily creating
||| WebGLRenderingContexts from JavaScript references.
webGlRenderingContextFromPointer : JSRef -> JS_IO $ Maybe WebGLRenderingContext
webGlRenderingContextFromPointer ref = let
    canvas   = jscall "%0.canvas"              (JSRef -> JS_IO JSRef) ref
    dbWidth  = jscall "%0.drawingBufferWidth"  (JSRef -> JS_IO JSRef) ref
    dbHeight = jscall "%0.drawingBufferHeight" (JSRef -> JS_IO JSRef) ref
  in
    case !(IdrisScript.pack !dbWidth) of
      (JSNumber ** w) => case !(IdrisScript.pack !dbHeight) of
        (JSNumber ** h) => map Just $ New <$> canvas <*>
                                              pure (fromJS w) <*>
                                              pure (fromJS h) <*>
                                              pure ref
        _               => pure Nothing
      _               => pure Nothing
