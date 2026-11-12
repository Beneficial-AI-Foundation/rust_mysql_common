import Defs

/-! Helper lemmas for the value-conversion proofs of group ConvInts (`Proofs/Value/Convert/`:
`ImplFromValueNum`, `IntoValueImpl`, `Bool`, `F32`, `F64`, `FromFloatBool`, ...). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.ConvInts

theorem byte_eq_iff (c : U8) (n : Nat) (hn : n < 256) : c = byte n ↔ c.val = n := by
  rw [UScalar.eq_equiv]
  have : (byte n).val = n := by
    show (BitVec.ofNat 8 n).toNat = n
    simp only [BitVec.toNat_ofNat]; omega
  rw [this]

/-- `bind` of a `ParseIrOpt`-valued `try_from` with the `commit` conversion. -/
theorem bind_commit {T : Type} (r : core.result.Result (value.convert.ParseIrOpt T) value.convert.FromValueError) :
    (match r with
      | core.result.Result.Ok x => do
        let t ← value.convert.ParseIrOpt.commit x
        ok (core.result.Result.Ok t)
      | core.result.Result.Err e => ok (core.result.Result.Err e)) =
    ok (match r with
      | .Ok (.Ready t) => .Ok t
      | .Ok (.Parsed t _) => .Ok t
      | .Err e => .Err e) := by
  rcases r with (_ | _) | _ <;> simp [value.convert.ParseIrOpt.commit]

theorem bmod_self (x : Int) (m : Nat) (h1 : -(m : Int) ≤ 2 * x) (h2 : 2 * x < m) : x.bmod m = x := by
  rw [Int.bmod]
  by_cases hx : 0 ≤ x
  · have : x % (m : Int) = x := Int.emod_eq_of_lt hx (by omega)
    rw [this]; split_ifs <;> omega
  · have : x % (m : Int) = x + m := by
      rw [← Int.add_emod_right]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]; split_ifs <;> omega

/-- The platform-dependent bounds, by platform width. -/
theorem platform_bounds :
    (System.Platform.numBits = 32 ∧ Isize.min = -2 ^ 31 ∧ Isize.max = 2 ^ 31 - 1 ∧ Usize.max = 2 ^ 32 - 1) ∨
    (System.Platform.numBits = 64 ∧ Isize.min = -2 ^ 63 ∧ Isize.max = 2 ^ 63 - 1 ∧ Usize.max = 2 ^ 64 - 1) := by
  simp only [Isize.min, Isize.max, Usize.max, Isize.numBits, Usize.numBits,
    IScalarTy.Isize_numBits_eq, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

/-! ## btoi agrees with `asciiInt` -/

theorem decimalDigits_eq (l : List U8) :
    Trusted.decimalDigits? l = if allDigits l then some (digitsVal l) else none := by
  rfl

theorem btoiValue_eq_asciiInt (l : List U8) : Trusted.btoiValue? l = asciiInt l := by
  cases l with
  | nil => rfl
  | cons c rest =>
    simp only [Trusted.btoiValue?, asciiInt, decimalDigits_eq]
    split_ifs <;> simp_all

theorem tryMkOpt_signed_map (ty : IScalarTy) (n : Int) :
    (IScalar.tryMkOpt ty n).map (fun x => x.val) =
      if IScalar.min ty ≤ n ∧ n ≤ IScalar.max ty then some n else none := by
  have h := IScalar.tryMkOpt_eq ty n
  have hmin : IScalar.min ty = -2 ^ (ty.numBits - 1) := by simp [IScalar.min]
  have hmax : IScalar.max ty = 2 ^ (ty.numBits - 1) - 1 := by simp [IScalar.max]
  rw [hmin, hmax]
  split at h <;> rename_i heq <;> rw [heq] <;> simp at h ⊢ <;> omega

theorem tryMkOpt_unsigned_map (ty : UScalarTy) (n : Nat) :
    (UScalar.tryMkOpt ty n).map (fun x => (x.val : Int)) =
      if n ≤ UScalar.max ty then some (n : Int) else none := by
  have h := UScalar.tryMkOpt_eq ty n
  have hmax : UScalar.max ty = 2 ^ ty.numBits - 1 := by simp [UScalar.max]
  have hpos : 0 < 2 ^ ty.numBits := by positivity
  rw [hmax]
  split at h <;> rename_i heq <;> rw [heq] <;> simp at h ⊢ <;> omega

theorem btoiSigned_map (ty : IScalarTy) (b : Slice U8) :
    (Trusted.btoiSigned ty b).map (fun x => x.val) =
      intConv (IScalar.min ty) (IScalar.max ty) (.bytes b.val) := by
  simp only [Trusted.btoiSigned, intConv, Val.integer, btoiValue_eq_asciiInt]
  cases asciiInt b.val with
  | none => rfl
  | some n => simpa using tryMkOpt_signed_map ty n

theorem btoiUnsigned_map (ty : UScalarTy) (b : Slice U8) :
    (Trusted.btoiUnsigned ty b).map (fun x => (x.val : Int)) =
      intConv 0 (UScalar.max ty) (.bytes b.val) := by
  simp only [Trusted.btoiUnsigned, intConv, Val.integer, btoiValue_eq_asciiInt]
  cases asciiInt b.val with
  | none => rfl
  | some n =>
    by_cases hn : 0 ≤ n
    · have := tryMkOpt_unsigned_map ty n.toNat
      simp only [Option.bind_some, hn, ite_true]
      rw [this]
      have : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg hn
      split_ifs <;> simp_all
    · simp [hn]

/-! ## Decimal text of integers -/

theorem u8sOf_append (a b : ByteArray) : Trusted.u8sOf (a ++ b) = Trusted.u8sOf a ++ Trusted.u8sOf b := by
  simp [Trusted.u8sOf, ByteArray.data_append]

theorem u8sOf_ascii (l : List Char) (h : ∀ c ∈ l, c.toNat < 128) :
    Trusted.u8sOf (String.ofList l).toUTF8 = l.map (fun c => byte c.toNat) := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.utf8Encode_cons, u8sOf_append, ih (fun d hd => h d (List.mem_cons_of_mem _ hd)),
      List.utf8Encode_singleton,
      String.utf8EncodeChar_eq_singleton (Char.utf8Size_eq_one_iff.mpr (by
        have : c.val.toNat < 128 := h c List.mem_cons_self
        rw [UInt32.le_iff_toNat_le]; exact Nat.le_of_lt_succ this))]
    simp only [List.map_cons]
    congr 1

theorem digit_bounds (m : Nat) (c : Char) (hc : c ∈ Nat.toDigits 10 m) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  have h := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : ('0'.val).toNat ≤ c.val.toNat := UInt32.le_iff_toNat_le.mp h.1
  have h2 : c.val.toNat ≤ ('9'.val).toNat := UInt32.le_iff_toNat_le.mp h.2
  exact ⟨h1, h2⟩

theorem toString_int (n : Int) :
    toString n = String.ofList ((if n < 0 then ['-'] else []) ++ Nat.toDigits 10 n.natAbs) := by
  cases n with
  | ofNat m => rfl
  | negSucc m =>
    show "-" ++ Nat.repr (m + 1) = _
    rw [Nat.repr_eq_ofList_toDigits]
    simp only [show Int.negSucc m < 0 from Int.negSucc_lt_zero m, ↓reduceIte]
    rw [String.ofList_append]
    rfl

theorem u8sOf_toString (n : Int) : Trusted.u8sOf (toString n).toUTF8 = decimalBytes n := by
  rw [toString_int, u8sOf_ascii, decimalBytes, List.map_append]
  · split_ifs <;> rfl
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · split_ifs at h <;> simp_all
    · have := digit_bounds _ c h; omega

theorem byte_val (k : Nat) (hk : k < 256) : (byte k).val = k := by
  show (BitVec.ofNat 8 k).toNat = k
  simp only [BitVec.toNat_ofNat]; omega

theorem allDigits_toDigits (m : Nat) :
    allDigits ((Nat.toDigits 10 m).map (fun c => byte c.toNat)) = true := by
  simp only [allDigits, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
  refine ⟨by simp [Nat.toDigits_ne_nil], ?_⟩
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  have := digit_bounds m c hc
  simp only [isDigit, byte_val c.toNat (by omega), Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem foldl_digits (l : List Char) (h : ∀ c ∈ l, c.toNat < 256) (init : Nat) :
    (l.map (fun c => byte c.toNat)).foldl (fun acc d => 10 * acc + (d.val - 48)) init =
      Nat.ofDigitChars 10 l init := by
  induction l generalizing init with
  | nil => rfl
  | cons c l ih =>
    simp only [List.map_cons, List.foldl_cons, Nat.ofDigitChars_cons]
    rw [byte_val _ (h c List.mem_cons_self), ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    rfl

theorem digitsVal_toDigits (m : Nat) :
    digitsVal ((Nat.toDigits 10 m).map (fun c => byte c.toNat)) = m := by
  rw [digitsVal, foldl_digits _ (fun c hc => by have := digit_bounds m c hc; omega)]
  exact Nat.ofDigitChars_ten_toDigits

theorem asciiInt_decimalBytes (n : Int) : asciiInt (decimalBytes n) = some n := by
  rw [decimalBytes]
  by_cases hn : n < 0
  · simp only [hn, ↓reduceIte, List.singleton_append, asciiInt, byte_val 45 (by omega)]
    simp only [show (45 : Nat) ≠ 43 by omega, ↓reduceIte, allDigits_toDigits, digitsVal_toDigits]
    congr 1; omega
  · simp only [hn, ↓reduceIte, List.nil_append]
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := n.natAbs) (b := 10))
    have hc := digit_bounds n.natAbs c (by rw [hcs]; exact List.mem_cons_self)
    have hall := allDigits_toDigits n.natAbs
    have hval := digitsVal_toDigits n.natAbs
    rw [hcs] at hall hval ⊢
    simp only [List.map_cons] at hall hval ⊢
    simp only [asciiInt, byte_val _ (by omega : c.toNat < 256)]
    simp only [show c.toNat ≠ 43 by omega, show c.toNat ≠ 45 by omega, hall, hval, ↓reduceIte]
    congr 1; omega

theorem integer_intVal (s : Bool) (n : Int) : (intVal s n).integer = some n := by
  unfold intVal
  split_ifs with h1 h2
  · rfl
  · simp only [Val.integer]; congr 1; omega
  · exact asciiInt_decimalBytes n

theorem decimalBytes_length (n : Int) (hn : n.natAbs < 2 ^ 128) : (decimalBytes n).length ≤ 40 := by
  have h : (Nat.toDigits 10 n.natAbs).length ≤ 39 :=
    (Nat.length_toDigits_le_iff (by decide) (by decide)).mpr (by
      have : (2 : Nat) ^ 128 < 10 ^ 39 := by decide
      omega)
  simp only [decimalBytes, List.length_append, List.length_map]
  split_ifs <;> simp <;> omega

theorem usize_max_ge : 2 ^ 32 - 1 ≤ Usize.max := by
  rcases platform_bounds with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> omega

/-- `i128::to_string` then `String::into_bytes`: the decimal text. -/
theorem string_into_bytes_toString (n : Int) (hn : n.natAbs < 2 ^ 128) :
    value.convert.trusted.string_into_bytes (toString n) ⦃ v => v.val = decimalBytes n ⦄ := by
  unfold value.convert.trusted.string_into_bytes
  rw [u8sOf_toString]
  have := decimalBytes_length n hn
  have := usize_max_ge
  rw [dite_eq_left_of_eq_true (eq_true (by omega)), WP.spec_ok, alloc.vec.Vec.from_val]

/-! ## The generic integer conversion -/

theorem spec_eq_ok {α : Type} {m : Result α} {p : α → Prop} (h : m ⦃ y => p y ⦄) : ∃ y, m = ok y ∧ p y := by
  cases m with
  | ret y => exact ⟨y, rfl, (WP.spec_ok y).mp h⟩
  | vis e k => exact ((WP.spec_vis e k).mp h).elim
  | div => exact (WP.spec_div.mp h).elim

/-- The postcondition of the integer `try_from`s. -/
abbrev TryPost {T : Type} (f : T → Int) (lo hi : Int) (v : value.Value)
    (r : core.result.Result (value.convert.ParseIrOpt T) value.convert.FromValueError) : Prop :=
  (okPart r).map (irView f) = intIr lo hi (Val.ofValue v) ∧
    (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v)

/-- `from_value_opt` (the default) of an integer type, from the spec of its `try_from`. -/
theorem from_value_opt_of_try {T : Type} (inst : value.convert.FromValue T (value.convert.ParseIrOpt T))
    (hinto : ∀ x, inst.coreconvertIntoInst.into x = value.convert.ParseIrOpt.commit x)
    (f : T → Int) (lo hi : Int) (v : value.Value)
    (h : inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v ⦃ r => TryPost f lo hi v r ⦄) :
    value.convert.FromValue.from_value_opt.default inst v ⦃ r =>
      (okPart r).map f = intConv lo hi (Val.ofValue v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  obtain ⟨r, hr, h1, h2, h3⟩ := spec_eq_ok h
  simp only [value.convert.FromValue.from_value_opt.default, hr, bind_ok]
  rcases r with (t | ⟨t, w⟩) | e
  · simp only [hinto, value.convert.ParseIrOpt.commit, bind_ok, WP.spec_ok]
    simp only [okPart, Option.map_some, irView, intIr] at h1
    cases hc : intConv lo hi (Val.ofValue v) <;> simp_all [okPart]
  · simp only [hinto, value.convert.ParseIrOpt.commit, bind_ok, WP.spec_ok]
    simp only [okPart, Option.map_some, irView, intIr] at h1
    cases hc : intConv lo hi (Val.ofValue v) <;> simp_all [okPart]
  · simp only [WP.spec_ok]
    simp only [okPart, Option.map_none, intIr] at h1
    have := h3 rfl
    cases hc : intConv lo hi (Val.ofValue v) <;> simp_all [okPart]

/-- `from_value` (the default), when the value converts. -/
theorem from_value_of_opt {T I : Type} (inst : value.convert.FromValue T I) (f : T → Int) (lo hi : Int)
    (v : value.Value) (n : Int)
    (h : inst.from_value_opt v ⦃ r => (okPart r).map f = intConv lo hi (Val.ofValue v) ∧ (okPart r = none → r = .Err v) ⦄)
    (hn : intConv lo hi (Val.ofValue v) = some n) :
    value.convert.FromValue.from_value.default inst v ⦃ x => f x = n ⦄ := by
  obtain ⟨r, hr, h1, _⟩ := spec_eq_ok h
  simp only [value.convert.FromValue.from_value.default, hr, bind_ok]
  rcases r with t | e
  · simp_all [okPart]
  · simp_all [okPart]

/-- `from_value` (the default) panics when the value does not convert. -/
theorem from_value_panic_of_opt {T I : Type} (inst : value.convert.FromValue T I) (f : T → Int) (lo hi : Int)
    (v : value.Value)
    (h : inst.from_value_opt v ⦃ r => (okPart r).map f = intConv lo hi (Val.ofValue v) ∧ (okPart r = none → r = .Err v) ⦄)
    (hn : intConv lo hi (Val.ofValue v) = none) :
    value.convert.FromValue.from_value.default inst v = fail .panic := by
  obtain ⟨r, hr, h1, _⟩ := spec_eq_ok h
  simp only [value.convert.FromValue.from_value.default, hr, bind_ok]
  rcases r with t | e
  · simp_all [okPart]
  · rfl

/-- `From<ParseIrOpt<T>> for Value` on the intermediate that `try_from` produced, from the spec
    of `From<T> for Value`. -/
theorem recover_ok {T : Type} (fromIr : value.convert.ParseIrOpt T → Result value.Value)
    (into : core.convert.Into T value.Value)
    (hfromIr : ∀ ir, fromIr ir = value.convert.ParseIrOpt.rollback into ir)
    (f : T → Int) (lo hi : Int) (signed : Bool) (v : value.Value) (ir : value.convert.ParseIrOpt T)
    (h : TryPost f lo hi v (.Ok ir))
    (hfrom : ∀ t, into.into t ⦃ w => Val.ofValue w = intVal signed (f t) ⦄) :
    fromIr ir ⦃ w => Val.ofValue w = intRecover lo hi signed (Val.ofValue v) ⦄ := by
  obtain ⟨h1, h2, _⟩ := h
  rw [hfromIr]
  rcases ir with t | ⟨t, w⟩
  · simp only [value.convert.ParseIrOpt.rollback]
    obtain ⟨w, hw, hw'⟩ := spec_eq_ok (hfrom t)
    rw [hw, WP.spec_ok, hw']
    simp only [okPart, Option.map_some, irView, intIr] at h1
    cases v <;> simp_all [Val.ofValue, intConv, Val.integer, intRecover]
  · simp only [value.convert.ParseIrOpt.rollback, WP.spec_ok]
    have := h2 t w rfl
    subst this
    simp only [okPart, Option.map_some, irView, intIr] at h1
    clear h2 hfrom hfromIr
    cases w <;> simp_all [Val.ofValue, intConv, Val.integer, intRecover]

/-- The error value of the integer `try_from`s. -/
theorem recover_err {T : Type} (f : T → Int) (lo hi : Int) (signed : Bool) (v : value.Value)
    (e : value.convert.FromValueError) (h : TryPost f lo hi v (.Err e)) :
    Val.ofValue e = intRecover lo hi signed (Val.ofValue v) := by
  obtain ⟨h1, _, h3⟩ := h
  have := h3 rfl
  simp only [core.result.Result.Err.injEq] at this
  subst this
  simp only [okPart, Option.map_none, intIr] at h1
  clear h3
  cases e <;> simp_all [Val.ofValue, intConv, Val.integer, intRecover]

/-- The `Bytes` branch of the integer `try_from`s, by the result of `btoi`. -/
theorem bytes_post {T : Type} (f : T → Int) (o : Option T) (b : alloc.vec.Vec U8) (lo hi : Int)
    (h : o.map f = intConv lo hi (.bytes b.val)) :
    (o = none → TryPost f lo hi (.Bytes b) (.Err (.Bytes b))) ∧
    (∀ x, o = some x → TryPost f lo hi (.Bytes b) (.Ok (.Parsed x (.Bytes b)))) := by
  constructor
  · intro ho
    subst ho
    simp only [Option.map_none] at h
    simp [TryPost, okPart, intIr, Val.ofValue, ← h]
  · intro x ho
    subst ho
    simp only [Option.map_some] at h
    simp [TryPost, okPart, intIr, Val.ofValue, ← h, irView]

/-- Round trip `from_value_opt::<T>(Value::from(x)) = Ok(x)`, from the specs of `From<T> for Value`
    and of `from_value_opt`. -/
theorem roundtrip_of {T I : Type} (fromT : T → Result value.Value) (inst : value.convert.FromValue T I)
    (f : T → Int) (lo hi : Int) (s : Bool) (x : T)
    (hfrom : fromT x ⦃ w => Val.ofValue w = intVal s (f x) ⦄)
    (hopt : ∀ v, value.convert.from_value_opt inst v ⦃ r =>
      (okPart r).map f = intConv lo hi (Val.ofValue v) ∧ (okPart r = none → r = .Err v) ⦄)
    (hinj : ∀ a b : T, f a = f b → a = b) (hr : lo ≤ f x ∧ f x ≤ hi) :
    (do let w ← fromT x; value.convert.from_value_opt inst w) ⦃ r => r = .Ok x ⦄ := by
  obtain ⟨w, hw, hw'⟩ := spec_eq_ok hfrom
  rw [hw, bind_ok]
  obtain ⟨r, hr', h1, _⟩ := spec_eq_ok (hopt w)
  rw [hr', WP.spec_ok]
  rw [hw', intConv, integer_intVal] at h1
  simp only [hr, and_self, ↓reduceIte] at h1
  rcases r with y | e
  · simp only [okPart, Option.map_some, Option.some.injEq] at h1
    rw [hinj y x h1]
  · simp [okPart] at h1

end mysql_common.ConvInts

open mysql_common in
/-- Closes the goals that `step*` leaves on the integer `try_from`s (after the casts). -/
macro "int_close" : tactic => `(tactic| (
  subst_vars
  simp_all [okPart, irView, intIr, intConv, Val.integer, Val.ofValue, UScalar.le_equiv, IScalar.le_equiv,
    IScalar.lt_equiv, I8.rMin, I8.rMax, I16.rMin, I16.rMax, I32.rMin, I32.rMax, I64.rMin, I64.rMax,
    I128.rMin, I128.rMax, U8.rMax, U16.rMax, U32.rMax, U64.rMax, U128.rMax,
    I8.min_eq, I8.max_eq, I16.min_eq, I16.max_eq, I32.min_eq, I32.max_eq, I64.min_eq, I64.max_eq,
    I128.min_eq, I128.max_eq, U8.max_eq, U16.max_eq, U32.max_eq, U64.max_eq, U128.max_eq]
  all_goals first
    | ((try simp (disch := scalar_tac) only [mysql_common.ConvInts.bmod_self] at *); scalar_tac)
    | (rcases mysql_common.ConvInts.platform_bounds with ⟨hp, h1, h2, h3⟩ | ⟨hp, h1, h2, h3⟩ <;>
        simp only [hp, h1, h2, h3] at * <;> norm_num at * <;>
        (try simp (disch := scalar_tac) only [mysql_common.ConvInts.bmod_self] at *) <;> scalar_tac)))


namespace mysql_common.ConvInts

/-! ## `From<T> for Value` of the integer types -/

theorem fromI8_spec (x : Std.I8) :
    value.Value.Insts.CoreConvertFromI8.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromI8.from]
  have hb := x.hBounds
  step*
  subst_vars
  simp only [Val.ofValue, intVal]
  split_ifs
  all_goals (try simp only [Val.int.injEq, Val.uint.injEq])
  all_goals first
    | scalar_tac
    | (simp (disch := scalar_tac) only [IScalar.cast_val_eq, UScalar.cast_val_eq, Nat.min_def, bmod_self]; scalar_tac)
    | (rcases platform_bounds with ⟨hp, h1, h2, h3⟩ | ⟨hp, h1, h2, h3⟩ <;>
        simp only [IScalar.cast_val_eq, UScalar.cast_val_eq, IScalarTy.Isize_numBits_eq,
          UScalarTy.Usize_numBits_eq, hp] at * <;> norm_num at * <;>
        (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

theorem fromU8_spec (x : Std.U8) :
    value.Value.Insts.CoreConvertFromU8.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromU8.from]
  have hb := x.hBounds
  step*
  subst_vars
  simp only [Val.ofValue, intVal]
  split_ifs
  all_goals (try simp only [Val.int.injEq, Val.uint.injEq])
  all_goals first
    | scalar_tac
    | (simp (disch := scalar_tac) only [IScalar.cast_val_eq, UScalar.cast_val_eq, Nat.min_def, bmod_self]; scalar_tac)
    | (rcases platform_bounds with ⟨hp, h1, h2, h3⟩ | ⟨hp, h1, h2, h3⟩ <;>
        simp only [IScalar.cast_val_eq, UScalar.cast_val_eq, IScalarTy.Isize_numBits_eq,
          UScalarTy.Usize_numBits_eq, hp] at * <;> norm_num at * <;>
        (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

theorem fromI16_spec (x : Std.I16) :
    value.Value.Insts.CoreConvertFromI16.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromI16.from]
  have hb := x.hBounds
  step*
  subst_vars
  simp only [Val.ofValue, intVal]
  split_ifs
  all_goals (try simp only [Val.int.injEq, Val.uint.injEq])
  all_goals first
    | scalar_tac
    | (simp (disch := scalar_tac) only [IScalar.cast_val_eq, UScalar.cast_val_eq, Nat.min_def, bmod_self]; scalar_tac)
    | (rcases platform_bounds with ⟨hp, h1, h2, h3⟩ | ⟨hp, h1, h2, h3⟩ <;>
        simp only [IScalar.cast_val_eq, UScalar.cast_val_eq, IScalarTy.Isize_numBits_eq,
          UScalarTy.Usize_numBits_eq, hp] at * <;> norm_num at * <;>
        (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

theorem fromU16_spec (x : Std.U16) :
    value.Value.Insts.CoreConvertFromU16.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromU16.from]
  have hb := x.hBounds
  step*
  subst_vars
  simp only [Val.ofValue, intVal]
  split_ifs
  all_goals (try simp only [Val.int.injEq, Val.uint.injEq])
  all_goals first
    | scalar_tac
    | (simp (disch := scalar_tac) only [IScalar.cast_val_eq, UScalar.cast_val_eq, Nat.min_def, bmod_self]; scalar_tac)
    | (rcases platform_bounds with ⟨hp, h1, h2, h3⟩ | ⟨hp, h1, h2, h3⟩ <;>
        simp only [IScalar.cast_val_eq, UScalar.cast_val_eq, IScalarTy.Isize_numBits_eq,
          UScalarTy.Usize_numBits_eq, hp] at * <;> norm_num at * <;>
        (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

theorem fromI32_spec (x : Std.I32) :
    value.Value.Insts.CoreConvertFromI32.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromI32.from]
  have hb := x.hBounds
  step*
  subst_vars
  simp only [Val.ofValue, intVal]
  split_ifs
  all_goals (try simp only [Val.int.injEq, Val.uint.injEq])
  all_goals first
    | scalar_tac
    | (simp (disch := scalar_tac) only [IScalar.cast_val_eq, UScalar.cast_val_eq, Nat.min_def, bmod_self]; scalar_tac)
    | (rcases platform_bounds with ⟨hp, h1, h2, h3⟩ | ⟨hp, h1, h2, h3⟩ <;>
        simp only [IScalar.cast_val_eq, UScalar.cast_val_eq, IScalarTy.Isize_numBits_eq,
          UScalarTy.Usize_numBits_eq, hp] at * <;> norm_num at * <;>
        (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

theorem fromU32_spec (x : Std.U32) :
    value.Value.Insts.CoreConvertFromU32.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromU32.from]
  have hb := x.hBounds
  step*
  subst_vars
  simp only [Val.ofValue, intVal]
  split_ifs
  all_goals (try simp only [Val.int.injEq, Val.uint.injEq])
  all_goals first
    | scalar_tac
    | (simp (disch := scalar_tac) only [IScalar.cast_val_eq, UScalar.cast_val_eq, Nat.min_def, bmod_self]; scalar_tac)
    | (rcases platform_bounds with ⟨hp, h1, h2, h3⟩ | ⟨hp, h1, h2, h3⟩ <;>
        simp only [IScalar.cast_val_eq, UScalar.cast_val_eq, IScalarTy.Isize_numBits_eq,
          UScalarTy.Usize_numBits_eq, hp] at * <;> norm_num at * <;>
        (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

theorem fromI64_spec (x : Std.I64) :
    value.Value.Insts.CoreConvertFromI64.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromI64.from]
  have hb := x.hBounds
  step*
  subst_vars
  simp only [Val.ofValue, intVal]
  split_ifs
  all_goals (try simp only [Val.int.injEq, Val.uint.injEq])
  all_goals first
    | scalar_tac
    | (simp (disch := scalar_tac) only [IScalar.cast_val_eq, UScalar.cast_val_eq, Nat.min_def, bmod_self]; scalar_tac)
    | (rcases platform_bounds with ⟨hp, h1, h2, h3⟩ | ⟨hp, h1, h2, h3⟩ <;>
        simp only [IScalar.cast_val_eq, UScalar.cast_val_eq, IScalarTy.Isize_numBits_eq,
          UScalarTy.Usize_numBits_eq, hp] at * <;> norm_num at * <;>
        (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

theorem fromU64_spec (x : Std.U64) :
    value.Value.Insts.CoreConvertFromU64.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromU64.from]
  have hb := x.hBounds
  step*
  subst_vars
  simp only [Val.ofValue, intVal]
  split_ifs
  all_goals (try simp only [Val.int.injEq, Val.uint.injEq])
  all_goals first
    | scalar_tac
    | (simp (disch := scalar_tac) only [IScalar.cast_val_eq, UScalar.cast_val_eq, Nat.min_def, bmod_self]; scalar_tac)
    | (rcases platform_bounds with ⟨hp, h1, h2, h3⟩ | ⟨hp, h1, h2, h3⟩ <;>
        simp only [IScalar.cast_val_eq, UScalar.cast_val_eq, IScalarTy.Isize_numBits_eq,
          UScalarTy.Usize_numBits_eq, hp] at * <;> norm_num at * <;>
        (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

theorem fromIsize_spec (x : Std.Isize) :
    value.Value.Insts.CoreConvertFromIsize.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromIsize.from]
  have hb := x.hBounds
  step*
  subst_vars
  simp only [Val.ofValue, intVal]
  split_ifs
  all_goals (try simp only [Val.int.injEq, Val.uint.injEq])
  all_goals first
    | scalar_tac
    | (simp (disch := scalar_tac) only [IScalar.cast_val_eq, UScalar.cast_val_eq, Nat.min_def, bmod_self]; scalar_tac)
    | (rcases platform_bounds with ⟨hp, h1, h2, h3⟩ | ⟨hp, h1, h2, h3⟩ <;>
        simp only [IScalar.cast_val_eq, UScalar.cast_val_eq, IScalarTy.Isize_numBits_eq,
          UScalarTy.Usize_numBits_eq, hp] at * <;> norm_num at * <;>
        (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

theorem fromUsize_spec (x : Std.Usize) :
    value.Value.Insts.CoreConvertFromUsize.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromUsize.from]
  have hb := x.hBounds
  step*
  subst_vars
  simp only [Val.ofValue, intVal]
  split_ifs
  all_goals (try simp only [Val.int.injEq, Val.uint.injEq])
  all_goals first
    | scalar_tac
    | (simp (disch := scalar_tac) only [IScalar.cast_val_eq, UScalar.cast_val_eq, Nat.min_def, bmod_self]; scalar_tac)
    | (rcases platform_bounds with ⟨hp, h1, h2, h3⟩ | ⟨hp, h1, h2, h3⟩ <;>
        simp only [IScalar.cast_val_eq, UScalar.cast_val_eq, IScalarTy.Isize_numBits_eq,
          UScalarTy.Usize_numBits_eq, hp] at * <;> norm_num at * <;>
        (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

theorem fromI128_spec (x : Std.I128) :
    value.Value.Insts.CoreConvertFromI128.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  have hb := x.hBounds
  have hs : (do
      let s ← value.convert.trusted.i128_to_string x
      let v ← value.convert.trusted.string_into_bytes s
      ok (value.Value.Bytes v)) ⦃ w => Val.ofValue w = .bytes (decimalBytes x.val) ⦄ := by
    simp only [value.convert.trusted.i128_to_string, bind_ok]
    have := string_into_bytes_toString x.val (by scalar_tac)
    obtain ⟨v, hv, hv'⟩ := spec_eq_ok this
    rw [hv, bind_ok, WP.spec_ok, Val.ofValue, hv']
  simp only [value.Value.Insts.CoreConvertFromI128.from]
  step*
  all_goals subst_vars
  all_goals first
    | (refine WP.spec_mono hs ?_
       intro w hw; rw [hw]; unfold intVal
       split_ifs <;> simp_all [IScalar.le_equiv, UScalar.le_equiv, IScalar.lt_equiv, I64.rMin, I64.rMax, U64.rMax] <;>
         scalar_tac)
    | (simp only [Val.ofValue, intVal]
       split_ifs <;> (try simp only [Val.int.injEq, Val.uint.injEq]) <;>
       simp_all [IScalar.le_equiv, UScalar.le_equiv, IScalar.lt_equiv, I64.rMin, I64.rMax, U64.rMax] <;>
       (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

theorem fromU128_spec (x : Std.U128) :
    value.Value.Insts.CoreConvertFromU128.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  have hb := x.hBounds
  have hs : (do
      let s ← value.convert.trusted.u128_to_string x
      let v ← value.convert.trusted.string_into_bytes s
      ok (value.Value.Bytes v)) ⦃ w => Val.ofValue w = .bytes (decimalBytes (x.val : ℤ)) ⦄ := by
    simp only [value.convert.trusted.u128_to_string, bind_ok]
    have := string_into_bytes_toString (x.val : ℤ) (by scalar_tac)
    obtain ⟨v, hv, hv'⟩ := spec_eq_ok this
    rw [show toString x.val = toString (x.val : ℤ) from rfl, hv, bind_ok, WP.spec_ok, Val.ofValue, hv']
  simp only [value.Value.Insts.CoreConvertFromU128.from]
  step*
  all_goals subst_vars
  all_goals first
    | (refine WP.spec_mono hs ?_
       intro w hw; rw [hw]; unfold intVal
       split_ifs <;> simp_all [IScalar.le_equiv, UScalar.le_equiv, IScalar.lt_equiv, I64.rMin, I64.rMax, U64.rMax] <;>
         scalar_tac)
    | (simp only [Val.ofValue, intVal]
       split_ifs <;> (try simp only [Val.int.injEq, Val.uint.injEq]) <;>
       simp_all [IScalar.le_equiv, UScalar.le_equiv, IScalar.lt_equiv, I64.rMin, I64.rMax, U64.rMax] <;>
       (try simp (disch := scalar_tac) only [bmod_self] at *) <;> scalar_tac)

end mysql_common.ConvInts
