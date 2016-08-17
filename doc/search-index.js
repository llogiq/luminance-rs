var searchIndex = {};
searchIndex["luminance"] = {"doc":"# What is this?","items":[[0,"blending","luminance","That module exports blending-related types and functions.",null,null],[4,"Equation","luminance::blending","Blending equation. Used to state how blending factors and pixel data should be blended.",null,null],[13,"Additive","","`Additive` represents the following blending equation:",0,null],[13,"Subtract","","`Subtract` represents the following blending equation:",0,null],[13,"ReverseSubtract","","Because subtracting is not commutative, `ReverseSubtract` represents the following additional\nblending equation:",0,null],[13,"Min","","`Min` represents the following blending equation:",0,null],[13,"Max","","`Max` represents the following blending equation:",0,null],[4,"Factor","","Blending factors. Pixel data are multiplied by these factors to achieve several effects driven\nby *blending equations*.",null,null],[13,"One","","`1 * color = factor`",1,null],[13,"Zero","","`0 * color = 0`",1,null],[13,"SrcColor","","`src * color`",1,null],[13,"SrcColorComplement","","`(1 - src) * color`",1,null],[13,"DestColor","","`dst * color`",1,null],[13,"DestColorComplement","","`(1 - dst) * color`",1,null],[13,"SrcAlpha","","`srcA * color`",1,null],[13,"SrcAlphaComplement","","`(1 - src) * color`",1,null],[13,"DstAlpha","","`dstA * color`",1,null],[13,"DstAlphaComplement","","`(1 - dstA) * color`",1,null],[13,"SrcAlphaSaturate","","",1,null],[11,"fmt","","",0,null],[11,"clone","","",0,null],[11,"fmt","","",1,null],[11,"clone","","",1,null],[0,"buffer","luminance","Static GPU typed arrays.",null,null],[3,"Buffer","luminance::buffer","A `Buffer` is a GPU region you can picture as an array. It has a static size and cannot be\nresized. The size is expressed in number of elements lying in the buffer, not in bytes.",null,null],[12,"repr","","",2,null],[12,"size","","",2,null],[4,"BufferError","","Buffer errors.",null,null],[13,"Overflow","","",3,null],[13,"TooFewValues","","",3,null],[13,"TooManyValues","","",3,null],[8,"HasBuffer","","Implement this trait to provide buffers.",null,null],[16,"ABuffer","","A type representing minimal information to operate on a buffer. For instance, a size, a\npointer, a method to retrieve data, a handle, whatever.",4,null],[10,"new","","Create a new buffer with a given size.",4,{"inputs":[{"name":"usize"}],"output":{"name":"abuffer"}}],[10,"free","","Destroy a buffer.",4,{"inputs":[{"name":"abuffer"}],"output":null}],[10,"write_whole","","Write values into the buffer.",4,null],[10,"write","","Write a single value in the buffer at a given offset.",4,{"inputs":[{"name":"abuffer"},{"name":"usize"},{"name":"t"}],"output":{"name":"result"}}],[10,"read_whole","","Read all values from the buffer.",4,{"inputs":[{"name":"abuffer"},{"name":"usize"}],"output":{"name":"vec"}}],[10,"read","","Read a single value from the buffer at a given offset.",4,{"inputs":[{"name":"abuffer"},{"name":"usize"}],"output":{"name":"option"}}],[11,"fmt","","",3,null],[11,"fmt","","",2,null],[11,"new","","Create a new `Buffer` with a given number of elements.",2,{"inputs":[{"name":"usize"}],"output":{"name":"buffer"}}],[11,"get","","Retrieve an element from the `Buffer`.",2,null],[11,"whole","","Retrieve the whole content of the `Buffer`.",2,null],[11,"set","","Set a value at a given index in the `Buffer`.",2,null],[11,"clear","","Fill the `Buffer` with a single value.",2,null],[11,"fill","","Fill the whole buffer with an array.",2,null],[11,"drop","","",2,null],[0,"chain","luminance","Generalized free tuples.",null,null],[3,"Chain","luminance::chain","The generalized free tuple.",null,null],[12,"0","","",5,null],[12,"1","","",5,null],[0,"framebuffer","luminance","Framebuffers and utility types and functions.",null,null],[3,"Framebuffer","luminance::framebuffer","Framebuffer with static layering, dimension, access and slots formats.",null,null],[12,"repr","","",6,null],[12,"color_slot","","",6,null],[12,"depth_slot","","",6,null],[3,"Slot","","Slot type; used to create color and depth slots for framebuffers.",null,null],[12,"texture","","",7,null],[4,"FramebufferError","","Framebuffer error.",null,null],[13,"Incomplete","","",8,null],[8,"HasFramebuffer","","Trait to implement to provide framebuffer features.",null,null],[16,"Framebuffer","","Framebuffer representation.",9,null],[10,"new_framebuffer","","Create a new framebuffer.",9,{"inputs":[{"name":"size"},{"name":"usize"}],"output":{"name":"result"}}],[10,"free_framebuffer","","Free a framebuffer.",9,{"inputs":[{"name":"framebuffer"}],"output":null}],[10,"default_framebuffer","","Default framebuffer.",9,{"inputs":[{"name":"size"}],"output":{"name":"framebuffer"}}],[8,"ColorSlot","","A framebuffer has a color slot. A color slot can either be empty (the *unit* type is used,`()`)\nor several color formats.",null,null],[10,"color_formats","","Turn a color slot into a list of pixel formats.",10,{"inputs":[],"output":{"name":"vec"}}],[10,"reify_textures","","Reify a list of raw textures into a color slot.",10,{"inputs":[{"name":"size"},{"name":"usize"},{"name":"vec"}],"output":{"name":"self"}}],[8,"DepthSlot","","A framebuffer has a depth slot. A depth slot can either be empty (the *unit* type is used, `()`)\nor a single depth format.",null,null],[10,"depth_format","","Turn a depth slot into a pixel format.",11,{"inputs":[],"output":{"name":"option"}}],[10,"reify_texture","","Reify a raw textures into a depth slot.",11,{"inputs":[{"name":"size"},{"name":"usize"},{"name":"option"}],"output":{"name":"self"}}],[11,"fmt","","",8,null],[11,"fmt","","",6,null],[11,"default","","",6,null],[11,"drop","","",6,null],[11,"new","","",6,{"inputs":[{"name":"size"},{"name":"usize"}],"output":{"name":"result"}}],[11,"color_formats","","",7,{"inputs":[],"output":{"name":"vec"}}],[11,"reify_textures","","",7,{"inputs":[{"name":"size"},{"name":"usize"},{"name":"vec"}],"output":{"name":"self"}}],[11,"color_formats","luminance::chain","",5,{"inputs":[],"output":{"name":"vec"}}],[11,"reify_textures","","",5,{"inputs":[{"name":"size"},{"name":"usize"},{"name":"vec"}],"output":{"name":"self"}}],[11,"depth_format","luminance::framebuffer","",7,{"inputs":[],"output":{"name":"option"}}],[11,"reify_texture","","",7,{"inputs":[{"name":"size"},{"name":"usize"},{"name":"option"}],"output":{"name":"self"}}],[0,"linear","luminance","Aliases types used to make it easier using long linear algebra types.",null,null],[6,"M22","luminance::linear","2x2 floating matrix.",null,null],[6,"M33","","3x3 floating matrix.",null,null],[6,"M44","","4x4 floating matrix.",null,null],[0,"pipeline","luminance","Dynamic rendering pipelines.",null,null],[3,"Pipeline","luminance::pipeline","A dynamic rendering pipeline. A *pipeline* is responsible of rendering into a `Framebuffer`.",null,null],[12,"framebuffer","","",12,null],[12,"clear_color","","",12,null],[12,"shading_commands","","",12,null],[3,"ShadingCommand","","A dynamic *shading command*. A shading command gathers *render commands* under a shader\n`Program`.",null,null],[12,"program","","",13,null],[12,"update","","",13,null],[12,"render_commands","","",13,null],[3,"RenderCommand","","A render command, which holds information on how to rasterize tessellation.",null,null],[12,"blending","","",14,null],[12,"depth_test","","",14,null],[12,"update","","",14,null],[12,"tessellation","","",14,null],[12,"instances","","",14,null],[12,"rasterization_size","","",14,null],[8,"HasPipeline","","Trait to implement to add `Pipeline` support.",null,null],[10,"run_pipeline","","",15,{"inputs":[{"name":"pipeline"}],"output":null}],[10,"run_shading_command","","",15,{"inputs":[{"name":"shadingcommand"}],"output":null}],[8,"SomeShadingCommand","","This trait is used to add existential quantification to `ShadingCommands`. It should be\nimplemented by backends to enable their use in `Pipeline`s.",null,null],[10,"run_shading_command","","",16,null],[11,"new","","",12,null],[11,"run","","Run a `Pipeline`.",12,null],[11,"run_shading_command","","",13,null],[11,"new","","",13,{"inputs":[{"name":"program"},{"name":"f"},{"name":"vec"}],"output":{"name":"self"}}],[11,"new","","",14,{"inputs":[{"name":"option"},{"name":"bool"},{"name":"f"},{"name":"tessellation"},{"name":"u32"},{"name":"option"}],"output":{"name":"self"}}],[0,"pixel","luminance","Pixel formats types and function manipulation.",null,null],[3,"PixelFormat","luminance::pixel","A `PixelFormat` gathers a `Type` along with a `Format`.",null,null],[12,"encoding","","",17,null],[12,"format","","",17,null],[3,"RGB8UI","","A red, green and blue 8-bit unsigned pixel format.",null,null],[3,"RGBA8UI","","A red, green, blue and alpha 8-bit unsigned pixel format.",null,null],[3,"RGB32F","","A red, green and blue 32-bit floating pixel format.",null,null],[3,"RGBA32F","","A red, green, blue and alpha 32-bit floating pixel format.",null,null],[3,"Depth32F","","A depth 32-bit floating pixel format.",null,null],[4,"Type","","Pixel type.",null,null],[13,"Integral","","",18,null],[13,"Unsigned","","",18,null],[13,"Floating","","",18,null],[4,"Format","","Format of a pixel.",null,null],[13,"R","","Holds a red-only channel.",19,null],[13,"RG","","Holds red and green channels.",19,null],[13,"RGB","","Holds red, green and blue channels.",19,null],[13,"RGBA","","Holds red, green, blue and alpha channels.",19,null],[13,"Depth","","Holds a depth channel.",19,null],[5,"is_color_pixel","","Does a `PixelFormat` represent a color?",null,{"inputs":[{"name":"pixelformat"}],"output":{"name":"bool"}}],[5,"is_depth_pixel","","Does a `PixelFormat` represent depth information?",null,{"inputs":[{"name":"pixelformat"}],"output":{"name":"bool"}}],[8,"Pixel","","Reify a static pixel format to runtime.",null,null],[16,"Encoding","","Encoding of a single pixel. It should match the `PixelFormat` mapping.",20,null],[16,"RawEncoding","","Raw encoding of a single pixel; i.e. that is, encoding of underlying values in contiguous\ntexture memory. It should be match the `PixelFormat` mapping.",20,null],[10,"pixel_format","","",20,{"inputs":[],"output":{"name":"pixelformat"}}],[8,"ColorPixel","","Constraint on `Pixel` for color ones.",null,null],[8,"DepthPixel","","Constraint on `Pixel` for depth ones.",null,null],[8,"RenderablePixel","","Constaint on `Pixel` for renderable ones.",null,null],[11,"fmt","","",17,null],[11,"clone","","",17,null],[11,"fmt","","",18,null],[11,"clone","","",18,null],[11,"fmt","","",19,null],[11,"clone","","",19,null],[11,"fmt","","",21,null],[11,"clone","","",21,null],[11,"pixel_format","","",21,{"inputs":[],"output":{"name":"pixelformat"}}],[11,"fmt","","",22,null],[11,"clone","","",22,null],[11,"pixel_format","","",22,{"inputs":[],"output":{"name":"pixelformat"}}],[11,"fmt","","",23,null],[11,"clone","","",23,null],[11,"pixel_format","","",23,{"inputs":[],"output":{"name":"pixelformat"}}],[11,"fmt","","",24,null],[11,"clone","","",24,null],[11,"pixel_format","","",24,{"inputs":[],"output":{"name":"pixelformat"}}],[11,"fmt","","",25,null],[11,"clone","","",25,null],[11,"pixel_format","","",25,{"inputs":[],"output":{"name":"pixelformat"}}],[0,"shader","luminance","Shader-related modules.",null,null],[0,"program","luminance::shader","Shader programs related types and functions.",null,null],[3,"Program","luminance::shader::program","A shader program with *uniform interface*.",null,null],[12,"repr","","",26,null],[12,"uniform_interface","","",26,null],[3,"ProgramProxy","","`Program` proxy used to map uniforms. When building a `Program`, as the `Program` doesn’t exist\nyet, a `ProgramProxy` is passed to act as it was the `Program`.",null,null],[4,"ProgramError","","",null,null],[13,"LinkFailed","","",27,null],[13,"InactiveUniform","","",27,null],[13,"UniformTypeMismatch","","",27,null],[8,"HasProgram","","Trait to implement to provide shader program features.",null,null],[16,"Program","","",28,null],[10,"new_program","","Create a new program by linking it with stages.",28,{"inputs":[{"name":"option"},{"name":"astage"},{"name":"option"},{"name":"astage"}],"output":{"name":"result"}}],[10,"free_program","","Free a program.",28,{"inputs":[{"name":"program"}],"output":null}],[10,"map_uniform","","Map a uniform name to its uniform representation. Can fail with `ProgramError`.",28,{"inputs":[{"name":"program"},{"name":"string"}],"output":{"name":"result"}}],[10,"update_uniforms","","Bulk update of uniforms. The update closure should contain the code used to update as many\nuniforms as wished.",28,{"inputs":[{"name":"program"},{"name":"f"}],"output":null}],[11,"fmt","","",26,null],[11,"drop","","",26,null],[11,"new","","Create a new `Program` by linking it with shader stages and by providing a function to build\nits *uniform interface*, which the `Program` will hold for you.",26,{"inputs":[{"name":"option"},{"name":"stage"},{"name":"option"},{"name":"stage"},{"name":"getuni"}],"output":{"name":"result"}}],[11,"update","","",26,null],[11,"fmt","","",29,null],[11,"uniform","","",29,null],[11,"fmt","","",27,null],[0,"stage","luminance::shader","",null,null],[3,"TessellationControlShader","luminance::shader::stage","",null,null],[3,"TessellationEvaluationShader","","",null,null],[3,"VertexShader","","",null,null],[3,"GeometryShader","","",null,null],[3,"FragmentShader","","",null,null],[3,"Stage","","A shader stage. The `T` type variable gives the type of the shader.",null,null],[12,"repr","","",30,null],[4,"Type","","A shader stage type.",null,null],[13,"TessellationControlShader","","",31,null],[13,"TessellationEvaluationShader","","",31,null],[13,"VertexShader","","",31,null],[13,"GeometryShader","","",31,null],[13,"FragmentShader","","",31,null],[4,"StageError","","",null,null],[13,"CompilationFailed","","Occurs when a shader fails to compile.",32,null],[13,"UnsupportedType","","Occurs when you try to create a shader which type is not supported on the current hardware.",32,null],[8,"HasStage","","",null,null],[16,"AStage","","",33,null],[10,"new_shader","","",33,{"inputs":[{"name":"type"},{"name":"str"}],"output":{"name":"result"}}],[10,"free_shader","","",33,{"inputs":[{"name":"astage"}],"output":null}],[8,"ShaderTypeable","","",null,null],[10,"shader_type","","",34,{"inputs":[],"output":{"name":"type"}}],[11,"fmt","","",31,null],[11,"clone","","",31,null],[11,"fmt","","",35,null],[11,"shader_type","","",35,{"inputs":[],"output":{"name":"type"}}],[11,"fmt","","",36,null],[11,"shader_type","","",36,{"inputs":[],"output":{"name":"type"}}],[11,"fmt","","",37,null],[11,"shader_type","","",37,{"inputs":[],"output":{"name":"type"}}],[11,"fmt","","",38,null],[11,"shader_type","","",38,{"inputs":[],"output":{"name":"type"}}],[11,"fmt","","",39,null],[11,"shader_type","","",39,{"inputs":[],"output":{"name":"type"}}],[11,"fmt","","",30,null],[11,"drop","","",30,null],[11,"new","","",30,{"inputs":[{"name":"str"}],"output":{"name":"result"}}],[11,"fmt","","",32,null],[11,"clone","","",32,null],[0,"uniform","luminance::shader","Shader uniforms and associated operations.",null,null],[3,"Uniform","luminance::shader::uniform","A shader uniform. `Uniform&lt;C, T&gt;` doesn’t hold any value. It’s more like a mapping between the\nhost code and the shader the uniform was retrieved from.",null,null],[12,"repr","","",40,null],[3,"UniformUpdate","","Wrapper over `Uniform`, discarding everything but update.",null,null],[8,"HasUniform","","",null,null],[16,"U","","Uniform representation.",41,null],[10,"update1_i32","","",41,{"inputs":[{"name":"u"},{"name":"i32"}],"output":null}],[10,"update2_i32","","",41,null],[10,"update3_i32","","",41,null],[10,"update4_i32","","",41,null],[10,"update1_slice_i32","","",41,null],[10,"update2_slice_i32","","",41,null],[10,"update3_slice_i32","","",41,null],[10,"update4_slice_i32","","",41,null],[10,"update1_u32","","",41,{"inputs":[{"name":"u"},{"name":"u32"}],"output":null}],[10,"update2_u32","","",41,null],[10,"update3_u32","","",41,null],[10,"update4_u32","","",41,null],[10,"update1_slice_u32","","",41,null],[10,"update2_slice_u32","","",41,null],[10,"update3_slice_u32","","",41,null],[10,"update4_slice_u32","","",41,null],[10,"update1_f32","","",41,{"inputs":[{"name":"u"},{"name":"f32"}],"output":null}],[10,"update2_f32","","",41,null],[10,"update3_f32","","",41,null],[10,"update4_f32","","",41,null],[10,"update1_slice_f32","","",41,null],[10,"update2_slice_f32","","",41,null],[10,"update3_slice_f32","","",41,null],[10,"update4_slice_f32","","",41,null],[10,"update22_f32","","",41,{"inputs":[{"name":"u"},{"name":"m22"}],"output":null}],[10,"update33_f32","","",41,{"inputs":[{"name":"u"},{"name":"m33"}],"output":null}],[10,"update44_f32","","",41,{"inputs":[{"name":"u"},{"name":"m44"}],"output":null}],[10,"update22_slice_f32","","",41,null],[10,"update33_slice_f32","","",41,null],[10,"update44_slice_f32","","",41,null],[10,"update1_bool","","",41,{"inputs":[{"name":"u"},{"name":"bool"}],"output":null}],[10,"update2_bool","","",41,null],[10,"update3_bool","","",41,null],[10,"update4_bool","","",41,null],[10,"update1_slice_bool","","",41,null],[10,"update2_slice_bool","","",41,null],[10,"update3_slice_bool","","",41,null],[10,"update4_slice_bool","","",41,null],[10,"update_textures","","",41,null],[8,"Uniformable","","Types that can behave as `Uniform`.",null,null],[10,"update","","",42,{"inputs":[{"name":"uniform"},{"name":"self"}],"output":null}],[11,"fmt","","",40,null],[11,"new","","",40,{"inputs":[{"name":"u"}],"output":{"name":"uniform"}}],[11,"update","","",40,null],[11,"from","","",43,{"inputs":[{"name":"uniform"}],"output":{"name":"self"}}],[11,"update","","Update the underlying `Uniform`.",43,null],[11,"contramap","","Apply a contravariant functor.",43,null],[11,"update","","",44,{"inputs":[{"name":"uniform"},{"name":"self"}],"output":null}],[11,"update","","",45,{"inputs":[{"name":"uniform"},{"name":"self"}],"output":null}],[11,"update","","",46,{"inputs":[{"name":"uniform"},{"name":"self"}],"output":null}],[0,"tessellation","luminance","Tessellation features.",null,null],[3,"Tessellation","luminance::tessellation","",null,null],[12,"repr","","",47,null],[4,"Mode","","Vertices can be connected via several modes.",null,null],[13,"Point","","",48,null],[13,"Line","","",48,null],[13,"LineStrip","","",48,null],[13,"Triangle","","",48,null],[13,"TriangleFan","","",48,null],[13,"TriangleStrip","","",48,null],[8,"HasTessellation","","Trait to implement to provide tessellation features.",null,null],[16,"Tessellation","","A type representing tessellation on GPU.",49,null],[10,"new","","Create a `Tessellation` from its vertices and a `Mode`.",49,null],[10,"destroy","","Destroy a `Tessellation`.",49,{"inputs":[{"name":"tessellation"}],"output":null}],[11,"fmt","","",48,null],[11,"clone","","",48,null],[11,"fmt","","",47,null],[11,"drop","","",47,null],[11,"new","","",47,null],[0,"texture","luminance","This module provides texture features.",null,null],[3,"Dim1","luminance::texture","",null,null],[3,"Dim2","","",null,null],[3,"Dim3","","",null,null],[3,"Cubemap","","",null,null],[3,"Flat","","",null,null],[3,"Layered","","",null,null],[3,"Texture","","Texture.",null,null],[12,"repr","","",50,null],[12,"size","","",50,null],[12,"mipmaps","","",50,null],[3,"Sampler","","A `Sampler` object gives hint on how a `Texture` should be sampled.",null,null],[12,"wrap_r","","How should we wrap around the *r* sampling coordinate?",51,null],[12,"wrap_s","","How should we wrap around the *s* sampling coordinate?",51,null],[12,"wrap_t","","How should we wrap around the *t* sampling coordinate?",51,null],[12,"minification","","Minification filter.",51,null],[12,"magnification","","Magnification filter.",51,null],[12,"depth_comparison","","For depth textures, should we perform depth comparison and if so, how?",51,null],[4,"Wrap","","How to wrap texture coordinates while sampling textures?",null,null],[13,"ClampToEdge","","If textures coordinates lay outside of *[0;1]*, they will be clamped to either *0* or *1* for\nevery components.",52,null],[13,"Repeat","","Textures coordinates are repeated if they lay outside of *[0;1]*. Picture this as:",52,null],[13,"MirroredRepeat","","Same as `Repeat` but it will alternatively repeat between *[0;1]* and *[1;0]*.",52,null],[4,"Filter","","Minification and magnification filter.",null,null],[13,"Nearest","","Clamp to nearest pixel.",53,null],[13,"Linear","","Linear interpolation with surrounding pixels.",53,null],[4,"DepthComparison","","Depth comparison to perform while depth test. `a` is the incoming fragment’s depth and b is the\nfragment’s depth that is already stored.",null,null],[13,"Never","","Depth test never succeeds.",54,null],[13,"Always","","Depth test always succeeds.",54,null],[13,"Equal","","Depth test succeeds if `a == b`.",54,null],[13,"NotEqual","","Depth test succeeds if `a != b`.",54,null],[13,"Less","","Depth test succeeds if `a &lt; b`.",54,null],[13,"LessOrEqual","","Depth test succeeds if `a &lt;= b`.",54,null],[13,"Greater","","Depth test succeeds if `a &gt; b`.",54,null],[13,"GreaterOrEqual","","Depth test succeeds if `a &gt;= b`.",54,null],[4,"Dim","","Dimension of a texture.",null,null],[13,"Dim1","","",55,null],[13,"Dim2","","",55,null],[13,"Dim3","","",55,null],[13,"Cubemap","","",55,null],[4,"CubeFace","","Faces of a cubemap.",null,null],[13,"PositiveX","","",56,null],[13,"NegativeX","","",56,null],[13,"PositiveY","","",56,null],[13,"NegativeY","","",56,null],[13,"PositiveZ","","",56,null],[13,"NegativeZ","","",56,null],[4,"Layering","","Texture layering. If a texture is layered, it has an extra coordinates to access the layer.",null,null],[13,"Flat","","Non-layered.",57,null],[13,"Layered","","Layered.",57,null],[5,"dim_capacity","","",null,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[8,"Dimensionable","","Reify a type into a `Dim`.",null,null],[16,"Size","","",58,null],[16,"Offset","","",58,null],[10,"dim","","Dimension.",58,{"inputs":[],"output":{"name":"dim"}}],[10,"width","","Width of the associated `Size`.",58,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[11,"height","","Height of the associated `Size`. If it doesn’t have one, set it to 1.",58,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[11,"depth","","Depth of the associated `Size`. If it doesn’t have one, set it to 1.",58,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[10,"x_offset","","X offset.",58,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[11,"y_offset","","Y offset. If it doesn’t have one, set it to 0.",58,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[11,"z_offset","","Z offset. If it doesn’t have one, set it to 0.",58,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[10,"zero_offset","","Zero offset.",58,{"inputs":[],"output":{"name":"offset"}}],[8,"Layerable","","Reify a type into a `Layering`.",null,null],[10,"layering","","",59,{"inputs":[],"output":{"name":"layering"}}],[8,"HasTexture","","Trait to implement to provide texture features.",null,null],[16,"ATexture","","",60,null],[10,"new_texture","","Create a new texture.",60,{"inputs":[{"name":"size"},{"name":"usize"},{"name":"sampler"}],"output":{"name":"atexture"}}],[10,"free","","Destroy a texture.",60,{"inputs":[{"name":"atexture"}],"output":null}],[10,"clear_part","","Clear the texture’s texels by setting them all to the same value.",60,{"inputs":[{"name":"atexture"},{"name":"bool"},{"name":"offset"},{"name":"size"},{"name":"encoding"}],"output":null}],[10,"upload_part","","Upload texels to the texture’s memory.",60,{"inputs":[{"name":"atexture"},{"name":"bool"},{"name":"offset"},{"name":"size"},{"name":"vec"}],"output":null}],[10,"upload_part_raw","","Upload raw texels to the texture’s memory.",60,{"inputs":[{"name":"atexture"},{"name":"bool"},{"name":"offset"},{"name":"size"},{"name":"vec"}],"output":null}],[10,"get_raw_texels","","Retrieve the texels as a collection of P::RawEncoding.",60,{"inputs":[{"name":"atexture"}],"output":{"name":"vec"}}],[11,"fmt","","",52,null],[11,"clone","","",52,null],[11,"fmt","","",53,null],[11,"clone","","",53,null],[11,"fmt","","",54,null],[11,"clone","","",54,null],[11,"fmt","","",55,null],[11,"clone","","",55,null],[11,"fmt","","",61,null],[11,"clone","","",61,null],[11,"dim","","",61,{"inputs":[],"output":{"name":"dim"}}],[11,"width","","",61,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[11,"x_offset","","",61,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[11,"zero_offset","","",61,{"inputs":[],"output":{"name":"offset"}}],[11,"fmt","","",62,null],[11,"clone","","",62,null],[11,"dim","","",62,{"inputs":[],"output":{"name":"dim"}}],[11,"width","","",62,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[11,"height","","",62,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[11,"x_offset","","",62,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[11,"y_offset","","",62,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[11,"zero_offset","","",62,{"inputs":[],"output":{"name":"offset"}}],[11,"fmt","","",63,null],[11,"clone","","",63,null],[11,"dim","","",63,{"inputs":[],"output":{"name":"dim"}}],[11,"width","","",63,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[11,"height","","",63,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[11,"depth","","",63,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[11,"x_offset","","",63,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[11,"y_offset","","",63,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[11,"z_offset","","",63,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[11,"zero_offset","","",63,{"inputs":[],"output":{"name":"offset"}}],[11,"fmt","","",64,null],[11,"clone","","",64,null],[11,"dim","","",64,{"inputs":[],"output":{"name":"dim"}}],[11,"width","","",64,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[11,"height","","",64,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[11,"depth","","",64,{"inputs":[{"name":"size"}],"output":{"name":"u32"}}],[11,"x_offset","","",64,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[11,"y_offset","","",64,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[11,"z_offset","","",64,{"inputs":[{"name":"offset"}],"output":{"name":"u32"}}],[11,"zero_offset","","",64,{"inputs":[],"output":{"name":"offset"}}],[11,"fmt","","",56,null],[11,"clone","","",56,null],[11,"fmt","","",57,null],[11,"clone","","",57,null],[11,"fmt","","",65,null],[11,"clone","","",65,null],[11,"layering","","",65,{"inputs":[],"output":{"name":"layering"}}],[11,"fmt","","",66,null],[11,"clone","","",66,null],[11,"layering","","",66,{"inputs":[],"output":{"name":"layering"}}],[11,"fmt","","",50,null],[11,"drop","","",50,null],[11,"new","","",50,{"inputs":[{"name":"size"},{"name":"usize"},{"name":"sampler"}],"output":{"name":"self"}}],[11,"from_raw","","",50,{"inputs":[{"name":"atexture"},{"name":"size"},{"name":"usize"}],"output":{"name":"self"}}],[11,"clear_part","","",50,null],[11,"clear","","",50,null],[11,"upload_part","","",50,null],[11,"upload","","",50,null],[11,"upload_part_raw","","",50,null],[11,"upload_raw","","",50,null],[11,"get_raw_texels","","",50,null],[11,"fmt","","",51,null],[11,"clone","","",51,null],[11,"default","","",51,{"inputs":[],"output":{"name":"self"}}],[0,"vertex","luminance","Vertex formats and associated types and functions.",null,null],[3,"VertexComponentFormat","luminance::vertex","A `VertexComponentFormat` gives hints about:",null,null],[12,"component_type","","",67,null],[12,"dim","","",67,null],[4,"Type","","Possible type of vertex components.",null,null],[13,"Integral","","",68,null],[13,"Unsigned","","",68,null],[13,"Floating","","",68,null],[13,"Boolean","","",68,null],[4,"Dim","","Possible dimension of vertex components.",null,null],[13,"Dim1","","",69,null],[13,"Dim2","","",69,null],[13,"Dim3","","",69,null],[13,"Dim4","","",69,null],[5,"vertex_format_size","","Retrieve the number of components in a `VertexFormat`.",null,{"inputs":[{"name":"vertexformat"}],"output":{"name":"usize"}}],[6,"VertexFormat","","A `VertexFormat` is a list of `VertexComponentFormat`s.",null,null],[8,"Vertex","","A type that can be used as a `Vertex` has to implement that trait – it must provide a mapping\nto `VertexFormat`.",null,null],[10,"vertex_format","","",70,{"inputs":[],"output":{"name":"vertexformat"}}],[11,"fmt","","",67,null],[11,"clone","","",67,null],[11,"fmt","","",68,null],[11,"clone","","",68,null],[11,"fmt","","",69,null],[11,"clone","","",69,null],[11,"vertex_format","luminance::chain","",5,{"inputs":[],"output":{"name":"vertexformat"}}],[14,"chain!","luminance","If your compiler supports the `type_macros`*feature*, you can use this macro to create chains\nwithout the syntactic nesting boilerplate.",null,null]],"paths":[[4,"Equation"],[4,"Factor"],[3,"Buffer"],[4,"BufferError"],[8,"HasBuffer"],[3,"Chain"],[3,"Framebuffer"],[3,"Slot"],[4,"FramebufferError"],[8,"HasFramebuffer"],[8,"ColorSlot"],[8,"DepthSlot"],[3,"Pipeline"],[3,"ShadingCommand"],[3,"RenderCommand"],[8,"HasPipeline"],[8,"SomeShadingCommand"],[3,"PixelFormat"],[4,"Type"],[4,"Format"],[8,"Pixel"],[3,"RGB8UI"],[3,"RGBA8UI"],[3,"RGB32F"],[3,"RGBA32F"],[3,"Depth32F"],[3,"Program"],[4,"ProgramError"],[8,"HasProgram"],[3,"ProgramProxy"],[3,"Stage"],[4,"Type"],[4,"StageError"],[8,"HasStage"],[8,"ShaderTypeable"],[3,"TessellationControlShader"],[3,"TessellationEvaluationShader"],[3,"VertexShader"],[3,"GeometryShader"],[3,"FragmentShader"],[3,"Uniform"],[8,"HasUniform"],[8,"Uniformable"],[3,"UniformUpdate"],[6,"M22"],[6,"M33"],[6,"M44"],[3,"Tessellation"],[4,"Mode"],[8,"HasTessellation"],[3,"Texture"],[3,"Sampler"],[4,"Wrap"],[4,"Filter"],[4,"DepthComparison"],[4,"Dim"],[4,"CubeFace"],[4,"Layering"],[8,"Dimensionable"],[8,"Layerable"],[8,"HasTexture"],[3,"Dim1"],[3,"Dim2"],[3,"Dim3"],[3,"Cubemap"],[3,"Flat"],[3,"Layered"],[3,"VertexComponentFormat"],[4,"Type"],[4,"Dim"],[8,"Vertex"]]};
initSearch(searchIndex);
