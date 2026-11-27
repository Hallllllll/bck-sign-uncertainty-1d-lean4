-- Generated from search/runs/d16-t2.30/000-float.json
-- SHA256 e8365023d6529b2bcd5c426d154e5546dc50de78dea0e4fc8486a164a6f5dc53

import NextProof.TailModes
import NextProof.TailInterval

namespace NextProof.Tail16
open Polynomial Tail
open scoped FourierTransform
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def weights : List ℤ := [
  -0x56805e21a580fdd0,
  0x60e05e792e0d92a0,
  0x8ac7230489e80000,
  0x2064e1cc6aee33f4,
  0x22d7589ecef2c64,
  -0x55011d2dd4d18f,
  0x4828c720d721a90,
  0x22f74ff9b4ef688,
  0x310f7e39f600412
]

def powers : List ℤ := [
  -0x116faee6fb2655ca51060d2aba04da7f0,
  -0xcf0cca22fcb525a94e53890c7ed963c200,
  0xf2b270b3249fef2e4c70e6c3419ac64a00,
  -0x9e14688ef07b41814e68964db4244b6800,
  0x586f9afde154a8ac3e606ff683e8e5bc00,
  -0x25fe8ca7f3e1a7fee275330f8dd2102000,
  0xb268913cbef503b5019cb4c47e3dd6000,
  -0x238f926725b58823eb5ee08ca7c4a8000,
  0x4ed6f215f4b118fcf2129112ef1e6000,
  -0x7bc576ccc239890baaef1b835160000,
  0x8ad6b61165dd0b96e371e88d260000,
  -0x6f21d999a0149f3d4292f51f80000,
  0x3eab715be108e4de4f143bfc0000,
  -0x1835466e512de48358982600000,
  0x61251ceb72cc08252ada00000,
  -0xe33d82e8f72fada5f800000,
  0xea9213852031376100000
]

def denominator : ℕ := 10000000000000000000

noncomputable def witness : ℚ[X] := C (1/(denominator : ℚ))*series 0 weights

theorem binding : intSeries weights = horner (X : ℤ[X]) powers := by
  exact bind_packed weights powers (2^147) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet2 : List ℤ := [
  -0xf667b540bf62fbbb9367759af618783f0,
  0x39dc776fe398d636d6e2b2556a45020600,
  -0x5ffb0f7829d3f28288feea6a66be48600,
  -0xd05f3098138a6c52789a1203ff19e8800,
  0x2bbcefc14bbf53f4b478bce4d2c0efc00,
  0x77f83c09edf71614b5db5834f4c66000,
  -0x68f13121cd51286049702513feba000,
  -0x163d1eb51e0219dfbe57764f1f448000,
  0x817eac68f2d815aa1cbc6a393ca6000,
  -0x16ab97eaa09cdf9562de52494be0000,
  0x268aaeece7a1f3f1de89c75db60000,
  -0x2a9a5d616dde56fdcf68ed3580000,
  0x1f337db73650b941416395bc0000,
  -0xef9ff33013b6a7ae311ae00000,
  0x483bb978bf70ce138daa00000,
  -0xc5eb4078532986b9d800000,
  0xea9213852031376100000
]

private theorem shift2 : horner (C (2 : ℤ)+X) powers = horner (X : ℤ[X]) jet2 := by
  exact shift_eq (B := 2^144) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet3 : List ℤ := [
  0x1a8e2451c48cf9c11a47893680ff131010,
  0x1384af93719900e030ced80c3570bcf200,
  -0x197a8c2c31e034afc5858411c2c87ad600,
  0x6a1c81e408b825ea9351c5e61c6c2800,
  0x3475699d14dfcaa0ed35cae2d73353c00,
  -0x4e335bdfddd7276f7422ac656904e000,
  -0x1b67f405449973484f1403ca8394a000,
  0x67cf04af35aeff8d3bb70b5fdd68000,
  0x9e41d36c8923793d61fe3df7866000,
  -0x636bef3204565d28bff94852da0000,
  0x10513839acb91d25291c2850c60000,
  -0x1761459ada2636106f5c37dc80000,
  0x148d9df512dfee726f315a7c0000,
  -0xb55e76c4d6a24d26a67ca00000,
  0x3d10e52ad8f876409f7a00000,
  -0xb7421f4001267343c800000,
  0xea9213852031376100000
]

private theorem shift3 : horner (C (3 : ℤ)+X) powers = horner (X : ℤ[X]) jet3 := by
  exact shift_eq (B := 2^146) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet4 : List ℤ := [
  0x17e6e63a038d102279f4c0d95bcee9f010,
  -0x1310b77f4bb6d7fd307848d6875338f200,
  -0x8ab2133ef6049d8658f10e9f73c4c1600,
  0x9412ff3ae4b491828cc0e68bf575c5800,
  0x10e5078505c9e0c1901506bdf518d3c00,
  -0x6b0b190f2c78e114c6f4856c21d72000,
  0xdb789606d5ec505f2a8ea15dedf6000,
  0x372b5d38737393c52600b533a018000,
  -0xcf04222d85fc1ccf979884ff19a000,
  -0xd1fbc901cb2e16dcfdede7a60000,
  0x4cea370074b5d4721cb78b6060000,
  -0xb18292166db4fd75157946b80000,
  0xc9f2ed6872bfc0078cbde7c0000,
  -0x84823e33c19d0b47f57f600000,
  0x32c1f9cf3f4e4c919c3a00000,
  -0xa898fe07af235fcdb800000,
  0xea9213852031376100000
]

private theorem shift4 : horner (C (4 : ℤ)+X) powers = horner (X : ℤ[X]) jet4 := by
  exact shift_eq (B := 2^148) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet5 : List ℤ := [
  0x61fe16c0c9b98ae4fad4c440c25329c10,
  -0x61d45f75cc12bc7e3fa81322b37930600,
  0x163fffc3b5483bd699577309e2ebdfba00,
  0xaab53605b5b72452857ceb415c0470800,
  0x7aa19f62459425f48b58e095e2efc00,
  0x59a6207c87aed4c9febe49cfdcda000,
  0x11cc8afad580b3599c7cc094f9706000,
  -0x1a32a98e0dd841a5b00fad9a6e38000,
  -0x5a8a9853a425310b49373b3795a000,
  0x129c114c04b13172dfccdbd33e0000,
  -0x190a8e91d58ff69a1f120a8a0000,
  -0x3e20875f12e167b6c94571280000,
  0x6f2eea66140f251376e29bc0000,
  -0x5c4adda8d17279b2b091200000,
  0x294ef765f272510683ea00000,
  -0x99efdccf5d204c57a800000,
  0xea9213852031376100000
]

private theorem shift5 : horner (C (5 : ℤ)+X) powers = horner (X : ℤ[X]) jet5 := by
  exact shift_eq (B := 2^150) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet6 : List ℤ := [
  0x210b1436077129deca7eec48f83b123410,
  0x46fc84ebb2dce20ab89256475838005600,
  0x37893eb4593c9f4b806602577f95db9a00,
  0xc1ece56e880ba6c45987f086d67ad3800,
  0xe56a1809bcaf63c529de7ba2cd887c00,
  0x42e8a2cd99bf85f9a453bc551a076000,
  0x21c8c318abe764b5e290afb6cbe6000,
  -0x22229344367be9d088eb940ed788000,
  0x2c3d4a3a7d4ad25286d02c4ef26000,
  0x95321d1340e7d023763cc55320000,
  -0x15741317fee8c97bab40b3dea0000,
  -0x362b539236505c8429664180000,
  0x31d612933548b175ce3ae3c0000,
  -0x3bf7e95002ee30076a1fe00000,
  0x20b7ddeef264839f568a00000,
  -0x8b46bb970b1d38e19800000,
  0xea9213852031376100000
]

private theorem shift6 : horner (C (6 : ℤ)+X) powers = horner (X : ℤ[X]) jet6 := by
  exact shift_eq (B := 2^151) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet7 : List ℤ := [
  0xacd827837c3a3b89bc759b763b2d1f7810,
  0xdf4f057b2ec1067034e896ed354709c200,
  0x63dc058b2c02754fd0e5f0f40f08fd8a00,
  0x123d386c120a771a088d787fa72d13e800,
  0x2188cfd2aca1ba9e05a8b5edb469dbc00,
  0x2fbb62414c478d3fbe2340e217d42000,
  -0x602853d98d2d01e02f5c2bdcaf6a000,
  -0xda67134d57a6abea9127b97dd8000,
  0x4693de7c1b15313599d06347be6000,
  -0x2ba86b82aeafef4112f014f6a0000,
  -0xea5047a0f7649519b0e81e1a0000,
  0x127336bb42c26e87b6114d780000,
  0xbccf9d53c62952738847fc0000,
  -0x22c8f55552dbc5e6b499a00000,
  0x18fcad6a3f24e45c141a00000,
  -0x7c9d9a5eb91a256b8800000,
  0xea9213852031376100000
]

private theorem shift7 : horner (C (7 : ℤ)+X) powers = horner (X : ℤ[X]) jet7 := by
  exact shift_eq (B := 2^153) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet11 : List ℤ := [
  0x119cf598a903cc87889568d8f941a2552010,
  0xa3818a654259784819b980b0c7e7e0d9200,
  0x26b28d05dfe9431bfd908c565833a02ea00,
  0x5229ca6cb853ca53e641178b5675e3a800,
  0x7d58f3c065f6b7b49a4035546281a3c00,
  0x9a8a066844a5f557481142a09b3d2000,
  0x93e4e375405bc79dfb2595ff76000,
  -0x1fb81933f581bfbdf0eab692a918000,
  -0xcf8a500f9f97dd6e606043249a000,
  0x777c51860cfab53bddc468d060000,
  0x5fab9e77d084bd769e1e92060000,
  -0xb3b1bdf221598a3ca78bf480000,
  -0x7fe6a089a145b75b22ce840000,
  0x99343787d134ea707b9600000,
  0x2a704ce723434b637ba00000,
  -0x41f9157d710dd7934800000,
  0xea9213852031376100000
]

private theorem shift11 : horner (C (11 : ℤ)+X) powers = horner (X : ℤ[X]) jet11 := by
  exact shift_eq (B := 2^158) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet20 : List ℤ := [
  0x35bf78c2af03f7bbba7aeb0f7fa9b50c4d010,
  0x1300c99c61ad247d1c47b96d6220ae74c4e00,
  0x3554b4be574e6454167b60bc443aa06c6a00,
  0x6d1c57c8ddbb8146aed0c051a5d0b6b5800,
  0x9e2dddded9a3342a60e00800c55cf33c00,
  0x291d8aad5d904f8439554647be16ce000,
  -0x18450f7b2ac53fe97ca06cda30df8a000,
  -0x2c969101b7fb32fd5ca805c2aace8000,
  -0xc1eb710c0716a03f9987ddbe79a000,
  0x322889e54617d39ff5a55b541a0000,
  0x39e626ddaed97c83857400f860000,
  0x4e112d7e09155ab879656480000,
  -0x1c8ea3c0f504a991e69bf840000,
  -0xf330d3d824156e341d3600000,
  0x2a704ce723434b637ba00000,
  0x41f9157d710dd7934800000,
  0xea9213852031376100000
]

private theorem shift20 : horner (C (20 : ℤ)+X) powers = horner (X : ℤ[X]) jet20 := by
  exact shift_eq (B := 2^166) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet28 : List ℤ := [
  0x28fa9088c8e7a6cdf43bb2e96b5ee4a0b1c010,
  0x7efbd5c5ae42de282ea03b39d84b73e74ee00,
  -0x33473740383c086f417a6fb7de2bb5295600,
  -0x26abad52f920ed69104ef1939843d6fd2800,
  0x69068b7b5bff51c6b9bab9b4b99e9e3c00,
  0x10c50538bc51c388004ef669a9410aee000,
  0x22a6349f05c2fdbe2f861e63ba117b6000,
  0x1986392ba0e8a19d165b7dcad40c98000,
  -0x9762911bd5c22cb91194b9a63a9a000,
  -0x1e78359073cd03d67a0abda54060000,
  -0x1064c66bc409f1c9140d2ac9ba0000,
  0x86ad17d25a3ba8cf0b4bb4c80000,
  0x10fbb06183163638344fd97c0000,
  0xafbeacffd17444ea6c62a00000,
  0x3d10e52ad8f876409f7a00000,
  0xb7421f4001267343c800000,
  0xea9213852031376100000
]

private theorem shift28 : horner (C (28 : ℤ)+X) powers = horner (X : ℤ[X]) jet28 := by
  exact shift_eq (B := 2^171) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet32 : List ℤ := [
  0x42f3065ccd06f70648a98bb44e57da58621810,
  0x888257747f4691e82a2b071fd7f75c74ebe00,
  0x32cca2f23bac6e669328633f6e9c2e81f4a00,
  0x15917d35dddb602f7ccf9f925191b89929800,
  0x3cf828793904080ccab073ef1514c151bc00,
  0x4cf3940cf638d9c0b4373529fa721f7e000,
  0x1249bc82d03564290c4588a0dc6cad6000,
  -0x3f3bd203e4fd144e54886d9cfbdea8000,
  -0x34b0b2dc679f4c4fee4f411611a1a000,
  0x36ea3436d3c50ec4d34eacf1a6a0000,
  0x8f077a63f369d70e114513b8260000,
  0x8aaea9d0305c13618f605a8080000,
  0x4fe2817a0c31617a9c3fdffc0000,
  0x1d8a86c11d62c56b7f855a00000,
  0x6ee3ac103faeea63d9da00000,
  0xf1e6a4214932c11c0800000,
  0xea9213852031376100000
]

private theorem shift32 : horner (C (32 : ℤ)+X) powers = horner (X : ℤ[X]) jet32 := by
  exact shift_eq (B := 2^173) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet37 : List ℤ := [
  0x2344f841536a4a5d0194097cf8a00a7f5b9dc10,
  0x13d7b3b6038dfb1cf7cc34f000f7cb30cbb7a00,
  0x5151b710d0955b1d21e8b576498e3d8e22ba00,
  0xa624f1570794bf0f8ad7e76477728b8c50800,
  0xab74a1946aaf8b17e30a82774b751532fc00,
  0x92e249536e5cd12fbe9de86ad77ec15a000,
  0x1b795e69fba6c52cc5352f54ebd7c606000,
  0x4b199d07acf53b7dd536265f69a37c8000,
  0x7944341300f41da078e770185662a6000,
  0x7ee790256486186789a071d846be0000,
  0x5bb834719300d7d1990a59c3e760000,
  0x2f14deb85c7b2077f0e8da28d80000,
  0x11399b9e5554a481a50cdd5bc0000,
  0x4687c22d419dbd8284306e00000,
  0xc07f1dfac03209b808ea00000,
  0x13b344a3ae342226a5800000,
  0xea9213852031376100000
]

private theorem shift37 : horner (C (37 : ℤ)+X) powers = horner (X : ℤ[X]) jet37 := by
  exact shift_eq (B := 2^175) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def jet72 : List ℤ := [
  0x10b8da3f34e3c3d28525aded3327f15228ee8586e4810,
  0x52bdc8f95d15bf21a4bdde70e1001740af7eca17de00,
  0xbe8eb719de303429d8eeab15f837139581f2f608a00,
  0x10f26959cfea93a238eba4c39f31e68d2e0a3d81800,
  0x10ad7328c7439cfc9a61b7c437a3c4cd3549e0bc00,
  0xc09b327ef15aeeddd8645534187029b26c61e000,
  0x69801cfe6e2071c57f8424fe12b5ddd47d16000,
  0x2cbe5525fc8c7d56a6df3f7306529b820d8000,
  0xeda234c343b567e5b64b1cac946022ee6000,
  0x3df52e0fd777294c24a8417844233ca0000,
  0xca64021ecf7c0f261001ecd8b93e60000,
  0x2005e6ab6fbfab1f82022e42d0880000,
  0x3d9afbace43ab0c2dde72604fc0000,
  0x57150dad5ffbae4db5e743a00000,
  0x5551031ee478e0f3bba9a00000,
  0x33c53d4ee19adcb8e8800000,
  0xea9213852031376100000
]

private theorem shift72 : horner (C (72 : ℤ)+X) powers = horner (X : ℤ[X]) jet72 := by
  exact shift_eq (B := 2^188) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem box0 (x : ℝ) (hl : (23/10 : ℝ) ≤ x) (hr : x ≤ (201/80 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 24) (b := 41) (q := 80) shift2 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box1 (x : ℝ) (hl : (201/80 : ℝ) ≤ x) (hr : x ≤ (109/40 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 41) (b := 58) (q := 80) shift2 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box2 (x : ℝ) (hl : (109/40 : ℝ) ≤ x) (hr : x ≤ (63/20 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 29) (b := 46) (q := 40) shift2 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box3 (x : ℝ) (hl : (63/20 : ℝ) ≤ x) (hr : x ≤ (4/1 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 3) (b := 20) (q := 20) shift3 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box4 (x : ℝ) (hl : (4/1 : ℝ) ≤ x) (hr : x ≤ (9/2 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 0) (b := 1) (q := 2) shift4 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box5 (x : ℝ) (hl : (9/2 : ℝ) ≤ x) (hr : x ≤ (5/1 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 1) (b := 2) (q := 2) shift4 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box6 (x : ℝ) (hl : (5/1 : ℝ) ≤ x) (hr : x ≤ (6/1 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 0) (b := 1) (q := 1) shift5 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box7 (x : ℝ) (hl : (6/1 : ℝ) ≤ x) (hr : x ≤ (7/1 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 0) (b := 1) (q := 1) shift6 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box8 (x : ℝ) (hl : (7/1 : ℝ) ≤ x) (hr : x ≤ (11/1 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 0) (b := 4) (q := 1) shift7 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box9 (x : ℝ) (hl : (11/1 : ℝ) ≤ x) (hr : x ≤ (20/1 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 0) (b := 9) (q := 1) shift11 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box10 (x : ℝ) (hl : (20/1 : ℝ) ≤ x) (hr : x ≤ (28/1 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 0) (b := 8) (q := 1) shift20 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box11 (x : ℝ) (hl : (28/1 : ℝ) ≤ x) (hr : x ≤ (32/1 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 0) (b := 4) (q := 1) shift28 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box12 (x : ℝ) (hl : (32/1 : ℝ) ≤ x) (hr : x ≤ (37/1 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 0) (b := 5) (q := 1) shift32 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem box13 (x : ℝ) (hl : (37/1 : ℝ) ≤ x) (hr : x ≤ (72/1 : ℝ)) : 0 < horner x powers := by
  exact interval_pos (a := 0) (b := 35) (q := 1) shift37 (by decide) (by decide) (by decide +kernel) x (by norm_num <;> linarith) (by norm_num <;> linarith)

private theorem beyond (x : ℝ) (hx : 72 ≤ x) : 0 < horner x powers := by
  exact ray_pos shift72 (by decide +kernel) (by decide +kernel) x (by exact_mod_cast hx)

theorem tail_integer (x : ℝ) (hx : (23/10 : ℝ) ≤ x) : 0 < horner x powers := by

  by_cases hr : x ≤ (201/80 : ℝ)
  · exact box0 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (109/40 : ℝ)
  · exact box1 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (63/20 : ℝ)
  · exact box2 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (4/1 : ℝ)
  · exact box3 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (9/2 : ℝ)
  · exact box4 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (5/1 : ℝ)
  · exact box5 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (6/1 : ℝ)
  · exact box6 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (7/1 : ℝ)
  · exact box7 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (11/1 : ℝ)
  · exact box8 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (20/1 : ℝ)
  · exact box9 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (28/1 : ℝ)
  · exact box10 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (32/1 : ℝ)
  · exact box11 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (37/1 : ℝ)
  · exact box12 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  by_cases hr : x ≤ (72/1 : ℝ)
  · exact box13 x hx hr
  replace hx := le_of_lt (lt_of_not_ge hr)

  exact beyond x (by linarith)

theorem eval_binding (x : ℝ) :
    horner x powers = ((fac (2*weights.length) : ℝ)*(denominator : ℝ))*witness.eval₂ (algebraMap ℚ ℝ) x :=
  eval_witness_binding weights denominator (by decide +kernel) powers binding x

theorem origin : witness.eval₂ (algebraMap ℚ ℝ) 0 < 0 := by
  have h := eval_binding 0
  have z : horner (0 : ℝ) powers < 0 := by
    change ((-0x116faee6fb2655ca51060d2aba04da7f0 : ℤ) : ℝ) + 0 * _ < 0
    norm_num
  rw [h] at z
  exact neg_of_mul_neg_right z (by positivity)


theorem tail (x : ℝ) (hx : (23/10 : ℝ) ≤ x) : 0 < witness.eval₂ (algebraMap ℚ ℝ) x := by
  have h := tail_integer x hx
  rw [eval_binding] at h
  exact pos_of_mul_pos_right h (by positivity)
theorem self_fourier : 𝓕 (radialGaussian witness) = radialGaussian witness := by
  rw [witness, radialGaussian_C_mul, fourier_const_mul, series_fourier]

end NextProof.Tail16
#print axioms NextProof.Tail16.origin
#print axioms NextProof.Tail16.tail
#print axioms NextProof.Tail16.self_fourier
