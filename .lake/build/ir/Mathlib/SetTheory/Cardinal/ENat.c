// Lean compiler output
// Module: Mathlib.SetTheory.Cardinal.ENat
// Imports: Init VerifiedAgora.tagger Mathlib.Algebra.Order.Hom.Ring Mathlib.Data.ENat.Basic Mathlib.SetTheory.Cardinal.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Cardinal_ofENatHom;
static lean_object* l_Cardinal_instCoeENat___closed__1;
extern lean_object* l_Cardinal_aleph0;
LEAN_EXPORT lean_object* l_Cardinal_ofENat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_Cardinal_ofENat___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_Cardinal_ofENat___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Cardinal_instCoeENat;
LEAN_EXPORT lean_object* l_Cardinal_ofENat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_Cardinal_ofENat___spec__1(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Cardinal_ofENat(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Cardinal_aleph0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Nat_cast___at_Cardinal_ofENat___spec__1(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_Cardinal_ofENat___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_cast___at_Cardinal_ofENat___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Cardinal_ofENat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Cardinal_ofENat(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Cardinal_instCoeENat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Cardinal_ofENat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Cardinal_instCoeENat() {
_start:
{
lean_object* x_1; 
x_1 = l_Cardinal_instCoeENat___closed__1;
return x_1;
}
}
static lean_object* _init_l_Cardinal_ofENatHom() {
_start:
{
lean_object* x_1; 
x_1 = l_Cardinal_instCoeENat___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_VerifiedAgora_tagger(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Order_Hom_Ring(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_ENat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_SetTheory_Cardinal_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_SetTheory_Cardinal_ENat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VerifiedAgora_tagger(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Order_Hom_Ring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_ENat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_SetTheory_Cardinal_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Cardinal_instCoeENat___closed__1 = _init_l_Cardinal_instCoeENat___closed__1();
lean_mark_persistent(l_Cardinal_instCoeENat___closed__1);
l_Cardinal_instCoeENat = _init_l_Cardinal_instCoeENat();
lean_mark_persistent(l_Cardinal_instCoeENat);
l_Cardinal_ofENatHom = _init_l_Cardinal_ofENatHom();
lean_mark_persistent(l_Cardinal_ofENatHom);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
