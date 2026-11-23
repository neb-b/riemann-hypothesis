module

public import Development.EtaleCohomology.TateTwists.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0013
public import Development.EtaleCohomology.TateTwists.Bundle0014

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.TtResSidePf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tensor_universal_property : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u

def tensor_quasi_isomorphism : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u

theorem tt_res_side_of (huniv : tensor_universal_property) (hqis : tensor_quasi_isomorphism) : tt_res_side := by
  intro q _ i I J M T e hI hJ hflat σ τ hσ hτ
  obtain ⟨hIge, ε, hε, hgen⟩ := hI
  obtain ⟨u, hu, -⟩ := (huniv (ZMod q) σ hσ).1 τ ε (𝟙 J)
  have := hIge
  have := hJ
  refine ⟨u, hqis (ZMod q) σ τ hσ hτ hflat ε u hu, fun U ζ b => ?_⟩
  rw [hu U 0 0 0 (add_zero 0), hgen U ζ]
  simp only [HomologicalComplex.id_f]
  rfl

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TtTensExPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

structure TensPre {R : Type} [CommRing R] (I J : Cx R) where
  P : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ
  e : ∀ (U : Scheme.{0}) (w : ℤ), Tens I J U w ≃ₗ[ULift.{1} R] (P.X w).obj (op U)
  nat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w),
    e V w (Tens.res g w x) = ((P.X w).map g.op).hom (e U w x)
  leibniz : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    ((P.d w (w + 1)).app (op U)).hom (e U w (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))) =
      e U (w + 1) (DirectSum.of _ ⟨(s + 1, t), by omega⟩ (Sec.map (I.d s (s + 1)) a ⊗ₜ b)) +
      s.negOnePow • e U (w + 1) (DirectSum.of _ ⟨(s, t + 1), by omega⟩ (a ⊗ₜ Sec.map (J.d t (t + 1)) b))

def tt_tens_pre : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), Nonempty (TensPre I J)

def tt_tens_sheafify : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), TensPre I J → ∃ (K : Cx R) (μ : Pair I J K), μ.IsTensor

theorem tt_tens_ex_of (hpre : tt_tens_pre) (hsh : tt_tens_sheafify) : tt_tens_ex := by
  intro R _ I J
  obtain ⟨T⟩ := hpre R I J
  exact hsh R I J T

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TtTwistSidePf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.TwSide

def tw_mul : Prop := ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ)

def tw_flat : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i)

def flip_ex : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧ (μ.IsTensor → ν.IsTensor)

def tens_qis : Prop := ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u

variable {R : Type} [CommRing R]

theorem sec_sub {F : Shv R} (h : IsZero F) (U : Scheme.{0}) : Subsingleton (Sec F U) := by
  constructor; intro a b
  have : 𝟙 F = 0 := h.eq_of_src _ _
  have ha : a = Sec.map (𝟙 F) a := rfl
  have hb : b = Sec.map (𝟙 F) b := rfl
  rw [ha, hb, this]; rfl

theorem flat_zero {F : Shv R} (h : IsZero F) : FlatS F := by
  refine ⟨F.obj, 𝟙 _, fun U y => LateralTheory.EtaleFoundations.TensFam.loc_top fun V g => ⟨Sec.res g y, rfl⟩,
    fun U x _ => LateralTheory.EtaleFoundations.TensFam.loc_top fun V g => @Subsingleton.elim _ (sec_sub h V) _ _, fun U _ => ?_⟩
  haveI := sec_sub h U
  infer_instance

open ZeroObject in
theorem flat_sgl {F : Shv R} (hF : FlatS F) (t : ℤ) : FlatS ((sgl F).X t) := by
  by_cases ht : t = 0
  · subst ht
    exact (show FlatS (if (0:ℤ) = 0 then F else 0) by rw [if_pos rfl]; exact hF)
  · exact flat_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)

theorem sgl_sub (F : Shv R) {t : ℤ} (ht : t ≠ 0) (U : Scheme.{0}) : Subsingleton (Sec ((sgl F).X t) U) :=
  sec_sub (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht) U

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)).symm

theorem map_comp' {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem map_zero' {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem tens_ind {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (P : Tens I J U w → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (ht : ∀ p a b, P (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b))) (x : Tens I J U w) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd _ _ hx hy
  | of p z =>
    induction z using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => simpa [DirectSum.lof_eq_of] using ht p a b
    | add z1 z2 h1 h2 => rw [map_add (f := _)]; exact hadd _ _ h1 h2

theorem lift_lof {I J K : Cx R} (τ : Pair I J K) (U : Scheme.{0}) (w : ℤ) p a b :
    τ.lift U w (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  simp [Pair.lift, DirectSum.toModule_lof]

theorem shv_isZero {F : Shv R} (h : ∀ U : Scheme.{0}, ∀ y : Sec F U, y = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U y
  exact h _ y

end LateralTheory.EtaleFoundations.TwSide

namespace LateralTheory.EtaleFoundations.TwSide
variable {q : ℕ} [NeZero q]

noncomputable def T {A B J : Cx (ZMod q)} (ε : B ⟶ J) (U : Scheme.{0}) (w : ℤ) :
    Tens A B U w →ₗ[ULift.{1} (ZMod q)] Tens A J U w :=
  DirectSum.toModule _ _ _ fun p => (DirectSum.lof (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = w}
      (fun p => Sec (A.X p.1.1) U ⊗[ULift.{1} (ZMod q)] Sec (J.X p.1.2) U) p).comp
    (TensorProduct.map LinearMap.id ((ε.f p.1.2).hom.app (op U)).hom)

theorem T_lof {A B J : Cx (ZMod q)} (ε : B ⟶ J) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (A.X p.1.1) U) (b : Sec (B.X p.1.2) U) :
    T ε U w (DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ Sec.map (ε.f p.1.2) b) := by
  simp [T, DirectSum.toModule_lof]

theorem smul_eq (c : ULift.{1} (ZMod q)) : c = ((c.down.val : ℕ) : ULift.{1} (ZMod q)) := by
  apply ULift.ext; rw [ULift.down_natCast, ZMod.natCast_zmod_val]

noncomputable def ofFam {F G : Shv (ZMod q)} (φ : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom
        { toFun := φ U.unop
          map_add' := map_add _
          map_smul' := fun c y => by
            rw [smul_eq c]
            simp only [Nat.cast_smul_eq_nsmul, map_nsmul, RingHom.id_apply] }
      naturality := fun U V g => by
        ext y
        exact (hφ V.unop U.unop g.unop y).symm }

theorem twist_side (htm : tw_mul) (htf : tw_flat) (hfl : flip_ex) (hqis : tens_qis) (i j k : ℤ) (hk : i + j = k)
    {J M : Cx (ZMod q)} (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U) (hJ : IsTwRes q j J e')
    (hflat : ∀ t, FlatS (J.X t)) (σ : Pair (sgl (tw q i)) J M) (hσ : σ.IsTensor) :
    IsTwRes q k M fun U ζ => σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) (e' U ζ) := by
  obtain ⟨μ, hμ, hgen⟩ := htm q i j k hk
  obtain ⟨hJge, ε', hε', hε'gen⟩ := hJ

  have hMge : M.IsStrictlyGE 0 := by
    refine (CochainComplex.isStrictlyGE_iff M 0).2 fun w hw => shv_isZero fun U y => ?_
    apply LateralTheory.EtaleFoundations.TensFam.sep
    obtain ⟨S, hS, h1⟩ := hσ.1 U w y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := h1 V g hg
    rw [← hx, show Sec.res g (0 : Sec (M.X w) U) = 0 from map_zero _]
    refine tens_ind (fun x => σ.lift V w x = 0) (map_zero _) (fun x y hx hy => by rw [map_add (f := _), hx, hy, add_zero])
      (fun p a b => ?_) x
    rw [lift_lof]
    rcases p with ⟨⟨s, t⟩, hst⟩
    by_cases hs : s = 0
    · have ht : t < 0 := by simp only at hst; omega
      haveI := sec_sub (CochainComplex.isZero_of_isStrictlyGE J 0 t (by omega)) V
      rw [Subsingleton.elim b 0, map_zero]
    · haveI := sgl_sub (tw q i) hs V
      rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
  let b : ∀ U : Scheme.{0}, Tens (sgl (tw q i)) (sgl (tw q j)) U 0 →+ Sec (M.X 0) U :=
    fun U => ((σ.lift U 0).comp (T ε' U 0)).toAddMonoidHom
  have hbv : ∀ U p a c, b U (DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ c)) =
      σ.mul U p.1.1 p.1.2 0 p.2 a (Sec.map (ε'.f p.1.2) c) := by
    intro U p a c
    simp only [b, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, T_lof, lift_lof]
  have hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g 0 x) := by
    intro V U g x
    refine tens_ind (fun x => Sec.res g (b U x) = b V (Tens.res g 0 x)) (by simp)
      (fun x y hx hy => by simp only [map_add (f := _), hx, hy]) (fun p a c => ?_) x
    rw [hbv, σ.nat, map_res]
    simp only [Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul]
    rw [hbv]
  obtain ⟨φ, hφnat, hφlift⟩ := LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing (ZMod q) (ZMod q) μ hμ 0 (M.X 0) b hb
  have hd : ∀ U (y : Sec ((sgl (tw q k)).X 0) U), Sec.map (M.d 0 (0 + 1)) (φ U y) = 0 := by
    intro U y
    apply LateralTheory.EtaleFoundations.TensFam.sep
    obtain ⟨S, hS, h1⟩ := hμ.1 U 0 y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := h1 V g hg
    rw [show Sec.res g (0 : Sec (M.X (0 + 1)) U) = 0 from map_zero _, map_res, hφnat, ← hx, hφlift]
    refine tens_ind (fun x => Sec.map (M.d 0 (0 + 1)) (b V x) = 0) (by simp)
      (fun x y hx hy => by simp only [map_add (f := _), hx, hy, add_zero]) (fun p a c => ?_) x
    rcases p with ⟨⟨s, t⟩, hst⟩
    rw [hbv]
    have hl := σ.leibniz V s t 0 hst a (Sec.map (ε'.f t) c)
    have hz : ∀ (F : Shv (ZMod q)) (m n : ℤ), (sgl F).d m n = 0 := fun F m n => HomologicalComplex.single_obj_d _ _ _ _ _
    rw [hl, ← map_comp', ε'.comm, map_comp', hz, hz]
    simp only [map_zero', map_zero, LinearMap.zero_apply, smul_zero, add_zero]
  let u : sgl (tw q k) ⟶ M := HomologicalComplex.mkHomFromSingle (sglι (tw q k) ≫ ofFam φ hφnat) (by
    intro l hl
    obtain rfl : l = 0 + 1 := by simp at hl; omega
    ext U y
    exact hd _ _)
  have hu0 : ∀ U (z : Sec ((sgl (tw q k)).X 0) U), Sec.map (u.f 0) z = φ U z := by
    intro U z
    rw [HomologicalComplex.mkHomFromSingle_f, ← Category.assoc]
    show Sec.map (ofFam φ hφnat) (Sec.map ((HomologicalComplex.singleObjXSelf _ 0 (tw q k)).hom ≫ (HomologicalComplex.singleObjXSelf _ 0 (tw q k)).inv) z) = _
    rw [Iso.hom_inv_id]; rfl
  have cmp : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q i)).X s) U) (c : Sec ((sgl (tw q j)).X t) U),
      Sec.map (u.f w) (μ.mul U s t w h a c) = σ.mul U s t w h a (Sec.map (ε'.f t) c) := by
    intro U s t w h a c
    by_cases hs : s = 0
    · by_cases ht : t = 0
      · subst hs ht
        obtain rfl : w = 0 := by omega
        rw [hu0]
        have := hφlift U (DirectSum.lof (ULift.{1} (ZMod q)) _ _ ⟨(0,0), h⟩ (a ⊗ₜ c))
        rw [lift_lof] at this
        rw [this, hbv]
      · haveI := sgl_sub (tw q j) ht U
        rw [Subsingleton.elim c 0]
        simp only [map_zero]
    · haveI := sgl_sub (tw q i) hs U
      rw [Subsingleton.elim a 0]
      simp only [map_zero, LinearMap.zero_apply]
  obtain ⟨μf, hμf, -, hμfT⟩ := hfl (ZMod q) μ
  obtain ⟨σf, hσf, -, hσfT⟩ := hfl (ZMod q) σ
  haveI := hJge
  haveI := hε'
  have hcomp : μf.Compat σf ε' (𝟙 _) u := by
    intro U s t w h a c
    rw [HomologicalComplex.id_f]
    show _ = σf.mul U s t w h (Sec.map (ε'.f s) a) c
    rw [hμf U t s w (by omega) c a, hσf U t s w (by omega) c _, Units.smul_def, Units.smul_def, ← cmp]
    exact map_zsmul ((u.f w).hom.app (op U)).hom _ _
  have hu : QuasiIso u := hqis (ZMod q) μf σf (hμfT hμ) (hσfT hσ) (flat_sgl (htf q i)) ε' u hcomp
  refine ⟨hMge, u, hu, fun U ζ => ?_⟩
  rw [← hgen U ζ, cmp, hε'gen]

end LateralTheory.EtaleFoundations.TwSide

theorem LateralTheory.EtaleFoundations.tt_twist_side_of (htm : LateralTheory.EtaleFoundations.TwSide.tw_mul) (htf : LateralTheory.EtaleFoundations.TwSide.tw_flat)
    (hfl : LateralTheory.EtaleFoundations.TwSide.flip_ex) (hqis : LateralTheory.EtaleFoundations.TwSide.tens_qis) : LateralTheory.EtaleFoundations.tt_twist_side := by
  intro q _ i j k hk J M e' hJ hflat σ hσ
  exact LateralTheory.EtaleFoundations.TwSide.twist_side htm htf hfl hqis i j k hk e' hJ hflat σ hσ
end

-- bundled from Development.EtaleCohomology.TateTwists.TwFGenInjPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwFInj

theorem prim_field {q : ℕ} {k : Type} [Field k] (ζ : Prim q k) : IsPrimitiveRoot ζ.1 q := by
  haveI : NeZero (q : k) := ⟨ζ.2.1.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := ζ.2.2
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int] using h

theorem pow_mod_eq {k : Type} [Field k] {q : ℕ} {z : k} (hz : IsPrimitiveRoot z q) (n : ℕ) :
    z ^ n = z ^ (n % q) := by
  conv_lhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hz.pow_eq_one, one_pow, mul_one]

theorem unit_unique {k : Type} [Field k] {q : ℕ} [NeZero q] {z : k} (hz : IsPrimitiveRoot z q)
    {u v : (ZMod q)ˣ} (h : z ^ (u : ZMod q).val = z ^ (v : ZMod q).val) : u = v :=
  Units.ext (ZMod.val_injective _ (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))

theorem exists_unit {k : Type} [Field k] {q : ℕ} [NeZero q] {z x : k} (hz : IsPrimitiveRoot z q)
    (hx : IsPrimitiveRoot x q) : ∃ u : (ZMod q)ˣ, x = z ^ (u : ZMod q).val := by
  obtain ⟨j, hj, hjx⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hc : j.Coprime q := (hz.pow_iff_coprime (NeZero.pos q) j).1 (hjx ▸ hx)
  refine ⟨ZMod.unitOfCoprime j hc, ?_⟩
  rw [← hjx]
  congr 1
  simp [ZMod.unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hj]

end LateralTheory.EtaleFoundations.TwFInj

namespace LateralTheory.EtaleFoundations.TwFInj

variable {q : ℕ} [NeZero q] {B : Type} [CommRing B] {k : Type} [Field k] (π : B →+* k) {z : k}
  (hz : IsPrimitiveRoot z q)

noncomputable def ex (ξ : Prim q B) : (ZMod q)ˣ := Classical.choose (exists_unit hz (prim_field (ξ.map π)))

theorem ex_spec (ξ : Prim q B) : π ξ.1 = z ^ (ex π hz ξ : ZMod q).val :=
  Classical.choose_spec (exists_unit hz (prim_field (ξ.map π)))

theorem ex_rel {ζ ξ : Prim q B} {a : (ZMod q)ˣ} (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ex π hz ξ = ex π hz ζ * a := by
  apply unit_unique hz
  rw [← ex_spec, h, map_pow, ex_spec π hz ζ, ← pow_mul, Units.val_mul, ZMod.val_mul, ← pow_mod_eq hz]

noncomputable def L (i : ℤ) : (Prim q B →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun ξ => ULift.up (((ex π hz ξ) ^ i : (ZMod q)ˣ) : ZMod q))

theorem twRel_le_ker (i : ℤ) : twRel q i B ≤ LinearMap.ker (L π hz i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, L, Finsupp.linearCombination_single, one_smul]
  apply ULift.ext
  simp [ex_rel π hz h, mul_zpow, mul_comm]

end LateralTheory.EtaleFoundations.TwFInj

theorem LateralTheory.EtaleFoundations.twF_gen_inj_of : LateralTheory.EtaleFoundations.twF_gen_inj := by
  intro q _ B _ hB i ζ c1 c2 hc
  simp only at hc
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI := Ideal.Quotient.field m
  let π := Ideal.Quotient.mk m
  have hz := LateralTheory.EtaleFoundations.TwFInj.prim_field (ζ.map π)
  let Φ := Submodule.liftQ _ (LateralTheory.EtaleFoundations.TwFInj.L π hz i) (LateralTheory.EtaleFoundations.TwFInj.twRel_le_ker π hz i)
  have h2 := congrArg Φ hc
  simp only [Φ, map_nsmul, Submodule.liftQ_apply, LateralTheory.EtaleFoundations.TwFInj.L, Finsupp.linearCombination_single, one_smul] at h2
  have h3 := congrArg ULift.down h2
  have h4 : (c1.val : ZMod q) * ((LateralTheory.EtaleFoundations.TwFInj.ex π hz ζ ^ i : (ZMod q)ˣ) : ZMod q) =
      (c2.val : ZMod q) * ((LateralTheory.EtaleFoundations.TwFInj.ex π hz ζ ^ i : (ZMod q)ˣ) : ZMod q) := by
    simp only [nsmul_eq_mul] at h3
    exact h3
  simpa [ZMod.natCast_zmod_val] using (Units.mul_left_inj _).1 h4
end

-- bundled from Development.EtaleCohomology.TateTwists.TwSecLocPfR
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨T, hT, hT'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (hQ : ∀ V (g : V ⟶ U), P V g → Loc V fun W h => Q W (h ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hS'⟩ := hP
  choose T hT hT' using fun V (g : V ⟶ U) (hg : S.arrows g) => hQ V g (hS' V g hg)
  refine ⟨Sieve.bind S.arrows T, Scheme.etaleTopology.bind_covering hS hT, ?_⟩
  rintro W _ ⟨V, h, g, hg, hh, rfl⟩
  exact hT' V g hg W h hh

theorem loc_surj {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : Sec (ofRings R M) U) :
    Loc U fun V g => ∃ x : M.obj Γ(V, ⊤), Sec.res g y = ofRings.sec M V x := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) y
  refine ⟨_, h, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, hx.symm⟩

end LateralTheory.EtaleFoundations.TwSecLocPf

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def ZarPow : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)),
  Loc V fun W h => ∃ a : (ZMod q)ˣ, (ξ.map h.appTop.hom).1 = (ζ.map h.appTop.hom).1 ^ (a : ZMod q).val

theorem ulift_smul_eq_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (m : M) : r • m = r.down.val • m := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    cases r with
    | up a =>
      change ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)
      rw [ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  exact Nat.cast_smul_eq_nsmul _ _ _

theorem twF_map_mk (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    ((twF q i).map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) x) : (twF q i).obj B) := rfl

theorem twF_single_pow (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (b : ULift.{1} (ZMod q)) :
    (Submodule.Quotient.mk (Finsupp.single ξ b) : (twF q i).obj A) =
      (b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj A) := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q i).obj A) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩)
  have e1 : Finsupp.single ξ b = b • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have e2 : Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e1, Submodule.Quotient.mk_smul, hrel, e2, Submodule.Quotient.mk_smul, smul_smul]
  exact ulift_smul_eq_nsmul _ _

theorem twF_loc (hZ : ZarPow) (q : ℕ) [NeZero q] (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤))
    (x : (twF q i).obj Γ(V, ⊤)) :
    Loc V fun W h => ∃ c : ℕ, ((twF q i).map h.appTop).hom x =
      c • (Submodule.Quotient.mk (Finsupp.single (ζ.map h.appTop.hom) 1) : (twF q i).obj Γ(W, ⊤)) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction f using Finsupp.induction with
  | zero =>
    refine loc_mono (loc_true V) fun W h _ => ⟨0, ?_⟩
    rw [zero_smul, Submodule.Quotient.mk_zero]
    exact map_zero ((twF q i).map h.appTop).hom
  | single_add ξ b g _ _ ih =>
    refine loc_mono (loc_and (hZ q V ζ ξ) ih) fun W h ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ =>
      ⟨(b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val + c, ?_⟩
    rw [Submodule.Quotient.mk_add]
    refine (map_add ((twF q i).map h.appTop).hom _ _).trans ?_
    rw [hc, twF_map_mk, Finsupp.mapDomain_single,
      twF_single_pow q i _ _ _ a ha b, add_smul]
    rfl

theorem TwSecLoc_of (hZ : ZarPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := by
  intro q _ i U ζ y
  refine loc_bind (loc_surj (twF q i) U y) fun V g ⟨x, hx⟩ => ?_
  refine loc_mono (twF_loc hZ q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
  have e : Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom := by
    apply Subtype.ext
    simp [Prim.map]
    rfl
  rw [e]
  refine (congrArg (fun z => ((tw q i).obj.map h.op).hom z) hx).trans ?_
  have hres : Sec.res h (ofRings.sec (twF q i) V x) =
      ofRings.sec (twF q i) W (((twF q i).map h.appTop).hom x) := by
    have hn := congrArg (fun f => f.hom x)
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality h.op)
    simp only [ModuleCat.hom_comp] at hn
    exact hn.symm
  refine hres.trans ?_
  rw [hc, ← hp]
  unfold twGen ofRings.sec
  exact map_nsmul _ _ _

end LateralTheory.EtaleFoundations.TwSecLocPf
end
end

