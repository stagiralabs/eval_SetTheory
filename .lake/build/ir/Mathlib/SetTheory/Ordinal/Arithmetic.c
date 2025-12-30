// Lean compiler output
// Module: Mathlib.SetTheory.Ordinal.Arithmetic
// Imports: Init VerifiedAgora.tagger Mathlib.Algebra.GroupWithZero.Divisibility Mathlib.Data.Nat.SuccPred Mathlib.Order.SuccPred.InitialSeg Mathlib.SetTheory.Cardinal.UnivLE Mathlib.SetTheory.Ordinal.Basic
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
static lean_object* l_Ordinal_familyOfBFamily_x27___rarg___closed__1;
LEAN_EXPORT lean_object* l_Ordinal_monoid;
LEAN_EXPORT lean_object* l_npowBinRec_go___at_Ordinal_monoid___spec__3___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily___boxed(lean_object*, lean_object*);
static lean_object* l_Ordinal_monoidWithZero___closed__1;
static lean_object* l_Ordinal_monoid___closed__2;
static lean_object* l_npowBinRec_go___at_Ordinal_monoid___spec__3___closed__1;
LEAN_EXPORT lean_object* l_npowBinRecAuto___at_Ordinal_monoid___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_npowBinRec_go___at_Ordinal_monoid___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordinal_monoid___lambda__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordinal_monoidWithZero;
LEAN_EXPORT lean_object* l_npowBinRec___at_Ordinal_monoid___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Ordinal_monoid___closed__1;
LEAN_EXPORT lean_object* l_Nat_binaryRec___at_Ordinal_monoid___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Ordinal_monoid___closed__3;
lean_object* l_Ordinal_typein(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily_x27___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Ordinal_monoid___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_npowBinRec_go___at_Ordinal_monoid___spec__3___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_binaryRec___at_Ordinal_monoid___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_land(x_7, x_2);
x_9 = lean_nat_dec_eq(x_8, x_5);
lean_dec(x_8);
x_10 = lean_nat_shiftr(x_2, x_7);
lean_dec(x_2);
if (x_9 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_box(0);
x_2 = x_10;
x_3 = x_11;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_box(0);
x_2 = x_10;
x_4 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_apply_2(x_1, x_3, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_npowBinRec_go___at_Ordinal_monoid___spec__3___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_npowBinRec_go___at_Ordinal_monoid___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_npowBinRec_go___at_Ordinal_monoid___spec__3___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_npowBinRec_go___at_Ordinal_monoid___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_npowBinRec_go___at_Ordinal_monoid___spec__3___closed__1;
x_5 = l_Nat_binaryRec___at_Ordinal_monoid___spec__4(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_npowBinRec___at_Ordinal_monoid___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_alloc_closure((void*)(l_npowBinRec_go___at_Ordinal_monoid___spec__3___lambda__1___boxed), 2, 0);
x_5 = l_Nat_binaryRec___at_Ordinal_monoid___spec__4(x_4, x_1, x_3, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_npowBinRecAuto___at_Ordinal_monoid___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_npowBinRec___at_Ordinal_monoid___spec__2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ordinal_monoid___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
static lean_object* _init_l_Ordinal_monoid___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Ordinal_monoid___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Ordinal_monoid___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_npowBinRecAuto___at_Ordinal_monoid___spec__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Ordinal_monoid___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Ordinal_monoid___closed__1;
x_3 = l_Ordinal_monoid___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Ordinal_monoid() {
_start:
{
lean_object* x_1; 
x_1 = l_Ordinal_monoid___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_npowBinRec_go___at_Ordinal_monoid___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_npowBinRec_go___at_Ordinal_monoid___spec__3___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ordinal_monoid___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Ordinal_monoid___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Ordinal_monoidWithZero___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Ordinal_monoid;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Ordinal_monoidWithZero() {
_start:
{
lean_object* x_1; 
x_1 = l_Ordinal_monoidWithZero___closed__1;
return x_1;
}
}
static lean_object* _init_l_Ordinal_familyOfBFamily_x27___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Ordinal_typein(lean_box(0), lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily_x27___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Ordinal_familyOfBFamily_x27___rarg___closed__1;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_apply_1(x_4, x_2);
x_6 = lean_apply_2(x_1, x_5, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Ordinal_familyOfBFamily_x27___rarg), 2, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Ordinal_familyOfBFamily_x27(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Ordinal_familyOfBFamily_x27___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Ordinal_familyOfBFamily___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Ordinal_familyOfBFamily___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Ordinal_familyOfBFamily(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_VerifiedAgora_tagger(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_GroupWithZero_Divisibility(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_SuccPred(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Order_SuccPred_InitialSeg(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_SetTheory_Cardinal_UnivLE(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_SetTheory_Ordinal_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_SetTheory_Ordinal_Arithmetic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VerifiedAgora_tagger(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_GroupWithZero_Divisibility(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_SuccPred(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Order_SuccPred_InitialSeg(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_SetTheory_Cardinal_UnivLE(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_SetTheory_Ordinal_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_npowBinRec_go___at_Ordinal_monoid___spec__3___closed__1 = _init_l_npowBinRec_go___at_Ordinal_monoid___spec__3___closed__1();
lean_mark_persistent(l_npowBinRec_go___at_Ordinal_monoid___spec__3___closed__1);
l_Ordinal_monoid___closed__1 = _init_l_Ordinal_monoid___closed__1();
lean_mark_persistent(l_Ordinal_monoid___closed__1);
l_Ordinal_monoid___closed__2 = _init_l_Ordinal_monoid___closed__2();
lean_mark_persistent(l_Ordinal_monoid___closed__2);
l_Ordinal_monoid___closed__3 = _init_l_Ordinal_monoid___closed__3();
lean_mark_persistent(l_Ordinal_monoid___closed__3);
l_Ordinal_monoid = _init_l_Ordinal_monoid();
lean_mark_persistent(l_Ordinal_monoid);
l_Ordinal_monoidWithZero___closed__1 = _init_l_Ordinal_monoidWithZero___closed__1();
lean_mark_persistent(l_Ordinal_monoidWithZero___closed__1);
l_Ordinal_monoidWithZero = _init_l_Ordinal_monoidWithZero();
lean_mark_persistent(l_Ordinal_monoidWithZero);
l_Ordinal_familyOfBFamily_x27___rarg___closed__1 = _init_l_Ordinal_familyOfBFamily_x27___rarg___closed__1();
lean_mark_persistent(l_Ordinal_familyOfBFamily_x27___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
