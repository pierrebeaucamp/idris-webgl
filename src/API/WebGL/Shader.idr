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

module API.WebGL.Shader

import IdrisScript

%access public export
%default total

record WebGLShader where
  constructor New
  self : JSRef

FRAGMENT_SHADER : Int
FRAGMENT_SHADER = 0x8B30

VERTEX_SHADER : Int
VERTEX_SHADER = 0x8B31


