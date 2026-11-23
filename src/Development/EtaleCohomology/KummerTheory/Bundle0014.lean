module

public import Development.EtaleCohomology.KummerTheory.Bundle0009
public import Development.EtaleCohomology.KummerTheory.Bundle0008
public import Development.EtaleCohomology.KummerTheory.Bundle0011

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.PlaceExPfZorn
section
noncomputable section

namespace LateralTheory.KummerTheory.PlaceZornPf

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem good_range : PlaceGood k K (LocalSubring.range (algebraMap k K)) := by
  refine ⟨fun c => ⟨c, rfl⟩, ?_⟩
  rintro a ⟨c, rfl⟩
  exact ⟨c, Or.inl rfl⟩

theorem ub (s : Set (LocalSubring K)) (hs : s ⊆ {A | PlaceGood k K A}) (H : IsChain (· ≤ ·) s)
    (y : LocalSubring K) (hys : y ∈ s) :
    ∃ U ∈ {A | PlaceGood k K A}, ∀ z ∈ s, z ≤ U := by
  have inst : Nonempty s := ⟨⟨y, hys⟩⟩
  have hdir := H.directed.mono_comp _ LocalSubring.toSubring_mono
  refine ⟨@LocalSubring.mk _ _ (⨆ i : s, i.1.toSubring) ⟨?_⟩, ?_, ?_⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ e
    obtain ⟨A, haA : a ∈ A.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
    obtain ⟨B, hbB : b ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := hdir A B
    refine (C.1.2.2 (a := ⟨a, hCA haA⟩) (b := ⟨b, hCB hbB⟩) (Subtype.ext congr(($e).1))).imp ?_ ?_
    · exact fun h ↦ h.map (Subring.inclusion (le_iSup (fun i : s ↦ i.1.toSubring) C))
    · exact fun h ↦ h.map (Subring.inclusion (le_iSup (fun i : s ↦ i.1.toSubring) C))
  · refine ⟨fun c => ?_, ?_⟩
    · exact le_iSup (fun i : s ↦ i.1.toSubring) ⟨y, hys⟩ ((hs hys).1 c)
    · intro a ha
      obtain ⟨A, haA : a ∈ A.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
      obtain ⟨c, hc⟩ := (hs A.2).2 a haA
      refine ⟨c, hc.imp_right fun hn hinv => hn ?_⟩
      obtain ⟨B, hbB : (a - algebraMap k K c)⁻¹ ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hinv
      obtain ⟨C, hCA, hCB⟩ := H.directed A B
      have hd : a - algebraMap k K c ∈ A.1.toSubring := sub_mem haA ((hs A.2).1 c)
      have hne : a - algebraMap k K c ≠ 0 := by
        intro h0; rw [h0, inv_zero] at hn; exact hn (zero_mem _)
      have hu : IsUnit (⟨a - algebraMap k K c, hCA.1 hd⟩ : C.1.toSubring) :=
        isUnit_iff_exists_inv.mpr ⟨⟨_, hCB.1 hbB⟩, Subtype.ext (by simp [mul_inv_cancel₀ hne])⟩
      have hu' : IsUnit (⟨a - algebraMap k K c, hd⟩ : A.1.toSubring) := by
        have := hCA.2
        apply IsUnit.of_map (Subring.inclusion hCA.1)
        exact hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu'
      have : (a - algebraMap k K c)⁻¹ = (w : K) :=
        inv_eq_of_mul_eq_one_right (by simpa using congrArg Subtype.val hw)
      rw [this]; exact w.2
  · intro A hA
    refine ⟨le_iSup (fun i : s ↦ i.1.toSubring) ⟨A, hA⟩, ⟨?_⟩⟩
    rintro ⟨a, haA⟩ h
    obtain ⟨⟨b, hb⟩, e⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨B, hbB : b ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := H.directed ⟨A, hA⟩ B
    apply hCA.2.1
    exact isUnit_iff_exists_inv.mpr ⟨⟨b, hCB.1 hbB⟩, Subtype.ext congr(($e).1)⟩

end LateralTheory.KummerTheory.PlaceZornPf

theorem LateralTheory.KummerTheory.PlaceZorn_of : LateralTheory.KummerTheory.PlaceZorn := by
  intro k K _ _ _ _
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ {A : LocalSubring K | LateralTheory.KummerTheory.PlaceGood k K A}
    (fun s hs H y hy => LateralTheory.KummerTheory.PlaceZornPf.ub s hs H y hy) _ LateralTheory.KummerTheory.PlaceZornPf.good_range
  exact ⟨m, hm.1, fun B hB hgB => hm.2 hgB hB⟩

theorem LateralTheory.KummerTheory.PlaceEx_of_step (h : LateralTheory.KummerTheory.PlaceStep) : LateralTheory.KummerTheory.PlaceEx :=
  LateralTheory.KummerTheory.PlaceEx_of LateralTheory.KummerTheory.PlaceZorn_of h
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.PrimIsPrimitiveRoot
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (f : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res f (twGen i ζ) = twGen i (Prim.map f.appTop.hom ζ) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality f.op
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤))
  simp only [ModuleCat.hom_comp] at h2
  unfold twGen ofRings.sec
  rw [← Finsupp.mapDomain_single]
  exact h2.symm

theorem twGen_zero_eq {q : ℕ} {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨c, hc⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hc
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem prim_isPrimitiveRoot {q : ℕ} {K : Type} [Field K] (μ : Prim q K) : IsPrimitiveRoot μ.1 q := by
  obtain ⟨z, hz1, hz2⟩ := μ
  have : NeZero (q : K) := ⟨hz1.ne_zero⟩
  refine (isRoot_cyclotomic_iff).1 ?_
  rw [aeval_def, algebraMap_int_eq] at hz2
  show Polynomial.eval z (cyclotomic q K) = 0
  rw [← map_cyclotomic_int, Polynomial.eval_map]
  exact hz2

theorem local_pow {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (x : U) :
    ∃ (h : Γ(U, ⊤)) (a : (ZMod q)ˣ), x ∈ U.basicOpen h ∧ h * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0 := by
  let e := (U.evaluation ⊤ x trivial).hom
  have hζ := prim_isPrimitiveRoot (Prim.map e ζ)
  have hξ := prim_isPrimitiveRoot (Prim.map e ξ)
  obtain ⟨i, hi, hie⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hcop : i.Coprime q := (hζ.pow_iff_coprime (NeZero.pos q) i).1 (hie ▸ hξ)
  have hav : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  obtain ⟨k, hk⟩ := binomExpansion ((X : Polynomial Γ(U, ⊤)) ^ q - 1) ξ.1
    (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1)
  have hξq := prim_pow ξ
  have hζq : (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, prim_pow ζ, one_pow]
  refine ⟨(q : Γ(U, ⊤)) * ξ.1 ^ (q - 1) + k * (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1),
    ZMod.unitOfCoprime i hcop, ?_, ?_⟩
  · rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x (show x ∈ (⊤ : U.Opens) from trivial)]
    have hy : e (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) = 0 := by
      rw [map_sub, map_pow, hav, sub_eq_zero]
      exact hie
    have hq : ((q : ℕ) : U.residueField x) ≠ 0 := (Prim.map e ξ).2.1.ne_zero
    change e _ ≠ 0
    rw [map_add (f := _), map_mul, map_mul, hy, mul_zero, add_zero, map_pow, map_natCast]
    exact mul_ne_zero hq (pow_ne_zero _ (hξ.ne_zero (NeZero.ne q)))
  · have hs : ξ.1 + (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) =
        ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val := by ring
    rw [hs] at hk
    simp only [eval_sub, eval_pow, eval_X, eval_one, hζq, hξq, sub_self, derivative_sub, derivative_X_pow,
      derivative_one, sub_zero, eval_mul, eval_C] at hk
    linear_combination hk

theorem sec_eq_of_cover {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} {ι : Type} (V : ι → U.Opens)
    (hV : TopologicalSpace.IsOpenCover V) (s t : Sec F U) (h : ∀ i, Sec.res (V i).ι s = Sec.res (V i).ι t) :
    s = t := by
  let S : Sieve U := {
    arrows := fun W f => Sec.res f s = Sec.res f t
    downward_closed := by
      intro W W' f hf g
      simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hf ⊢
      rw [hf] }
  have hS : S ∈ Scheme.etaleTopology U := by
    apply Scheme.zariskiTopology_le_etaleTopology
    refine Scheme.zariskiTopology.superset_covering ?_
      (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover V hV))
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro W f ⟨i⟩
    exact h i
  have hsh : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _) F.property)
  exact (hsh S hS).isSeparatedFor.ext fun W f hf => hf

theorem twGen_zero_indep {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) :
    twGen 0 ξ = twGen 0 ζ := by
  choose h a hx hh using fun x : U => local_pow ζ ξ x
  refine sec_eq_of_cover (fun x => U.basicOpen (h x)) ?_ _ _ fun x => ?_
  · refine eq_top_iff.2 fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hx y⟩
  rw [twGen_res, twGen_res]
  apply twGen_zero_eq _ _ (a x)
  change (U.basicOpen (h x)).ι.appTop.hom ξ.1 = (U.basicOpen (h x)).ι.appTop.hom ζ.1 ^ _
  rw [← map_pow, ← sub_eq_zero, ← map_sub]
  have hu : IsUnit ((U.basicOpen (h x)).ι.appTop.hom (h x)) := by
    rw [Scheme.Opens.ι_appTop]
    have key : ∀ (W : U.Opens) (hW : W = U.basicOpen (h x)) (hle : W ≤ ⊤),
        IsUnit (U.presheaf.map (homOfLE hle).op (h x)) := by
      rintro W rfl hle
      exact RingedSpace.isUnit_res_basicOpen U.toRingedSpace (h x)
    exact key _ (Scheme.Opens.ι_image_top _) _
  exact hu.mul_right_eq_zero.1 (by rw [← map_mul, hh x, map_zero])

theorem TwRes0_of : TwRes0 := by
  intro q _ U X x ζ₀ ζ
  rw [twGen_res]
  exact twGen_zero_indep _ _

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.PrimTorsPf
section
noncomputable section
open Polynomial IsLocalRing GlobalTheory.EtC

namespace LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem aeval_cyc {S : Type} [CommRing S] (q : ℕ) (x : S) :
    aeval x (cyclotomic q ℤ) = eval x (cyclotomic q S) := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, map_cyclotomic_int]

theorem prim_pow {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem pow_mod_q {q : ℕ} {B : Type} [CommRing B] {x : B} (h : x ^ q = 1) (n : ℕ) : x ^ n = x ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, h, one_pow, one_mul]

variable {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B]

theorem neZero_res (hq : IsUnit (q : B)) : NeZero (q : ResidueField B) :=
  ⟨by simpa using (hq.map (residue B)).ne_zero⟩

theorem uniq (hq : IsUnit (q : B)) {u v : B} (hu : u ^ q = 1) (hv : v ^ q = 1)
    (h : residue B u = residue B v) : u = v := by
  have hq' := neZero_res hq
  have hS : IsUnit (∑ i ∈ Finset.range q, u ^ i * v ^ (q - 1 - i)) := by
    apply isUnit_of_map_unit (residue B)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, map_pow, h]
    rw [geom_sum₂_self]
    have hv' : residue B v ^ q = 1 := by rw [← map_pow, hv, map_one]
    have hu1 : IsUnit (residue B v) := IsUnit.of_pow_eq_one hv' (NeZero.ne q)
    exact (isUnit_iff_ne_zero.2 (NeZero.ne _)).mul (hu1.pow _)
  have e := geom_sum₂_mul u v q
  rw [hu, hv, sub_self] at e
  exact sub_eq_zero.1 ((hS.mul_right_eq_zero).1 e)

theorem prim_res (hq : IsUnit (q : B)) (ζ : Prim q B) : IsPrimitiveRoot (residue B ζ.1) q := by
  have := neZero_res hq
  rw [← isRoot_cyclotomic_iff, IsRoot, ← aeval_cyc]
  have e := Polynomial.aeval_algHom_apply (residue B).toIntAlgHom ζ.1 (cyclotomic q ℤ)
  rw [ζ.2.2, map_zero] at e
  exact e

theorem exists_idx (hq : IsUnit (q : B)) (ζ ξ : Prim q B) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  have hζ := prim_res hq ζ
  have hξ := prim_res hq ξ
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hc : i.Coprime q := (hζ.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (he ▸ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hc : (ZMod q)ˣ) : ZMod q).val = i := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  refine uniq hq (prim_pow ξ) (by rw [← pow_mul, mul_comm, pow_mul, prim_pow ζ, one_pow]) ?_
  rw [map_pow, he]

theorem idx_unique (hq : IsUnit (q : B)) (ζ : Prim q B) {a b : (ZMod q)ˣ}
    (h : ζ.1 ^ (a : ZMod q).val = ζ.1 ^ (b : ZMod q).val) : a = b := by
  have h' := congrArg (residue B) h
  rw [map_pow, map_pow] at h'
  exact Units.ext (ZMod.val_injective q ((prim_res hq ζ).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h'))

theorem idx_mul {ζ0 ζ ξ : Prim q B} {a b : (ZMod q)ˣ} (hb : ζ.1 = ζ0.1 ^ (b : ZMod q).val)
    (ha : ξ.1 = ζ.1 ^ (a : ZMod q).val) : ξ.1 = ζ0.1 ^ ((a * b : (ZMod q)ˣ) : ZMod q).val := by
  rw [Units.val_mul, ZMod.val_mul, ← pow_mod_q (prim_pow ζ0), ha, hb, ← pow_mul, mul_comm]

end LateralTheory.KummerTheory.PrimitiveRootTorsion

namespace LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem exists_prim {q : ℕ} [NeZero q] {B : Type} [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (ResidueField B)] (hq : IsUnit (q : B)) : Nonempty (Prim q B) := by
  have := neZero_res hq
  obtain ⟨μ, hμ⟩ := IsSepClosed.exists_root (cyclotomic q (ResidueField B))
    (degree_cyclotomic_pos q _ (Nat.pos_of_ne_zero (NeZero.ne q))).ne' (separable_cyclotomic q _)
  obtain ⟨a0, rfl⟩ := residue_surjective μ
  have hev : residue B (eval a0 (cyclotomic q B)) = eval (residue B a0) (cyclotomic q (ResidueField B)) := by
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, map_cyclotomic]
  have hder : residue B (eval a0 (derivative (cyclotomic q B))) =
      eval (residue B a0) (derivative (cyclotomic q (ResidueField B))) := by
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, ← Polynomial.derivative_map, map_cyclotomic]
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (cyclotomic q B) (cyclotomic.monic q B) a0
    (by rw [← residue_eq_zero_iff, hev]; exact hμ)
    (by
      apply isUnit_of_map_unit (residue B)
      rw [hder, isUnit_iff_ne_zero]
      have h := (separable_cyclotomic q (ResidueField B)).aeval_derivative_ne_zero
        (x := residue B a0) (by rw [Polynomial.coe_aeval_eq_eval]; exact hμ)
      rwa [Polynomial.coe_aeval_eq_eval] at h)
  exact ⟨⟨a, hq, by rw [aeval_cyc]; exact ha⟩⟩

end LateralTheory.KummerTheory.PrimitiveRootTorsion

namespace LateralTheory.KummerTheory
open LateralTheory.KummerTheory.PrimitiveRootTorsion

theorem PrimTors_of : PrimTors := by
  intro q _ B _ hSH hq
  obtain ⟨_, _⟩ := hSH
  refine ⟨exists_prim hq, fun i ζ => ?_⟩
  classical
  have hex : ∀ ξ : Prim q B, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := fun ξ => exists_idx hq ζ ξ
  let ind : Prim q B → (ZMod q)ˣ := fun ξ => (hex ξ).choose
  have hind : ∀ ξ, ξ.1 = ζ.1 ^ (ind ξ : ZMod q).val := fun ξ => (hex ξ).choose_spec
  let v : Prim q B → ULift.{1} (ZMod q) := fun ξ => ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)
  let φ := Finsupp.linearCombination (ULift.{1} (ZMod q)) v
  have hker : twRel q i B ≤ LinearMap.ker φ := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ', ξ, a, h, rfl⟩
    have hi : ind ξ = a * ind ζ' := idx_unique hq ζ (by rw [← hind ξ]; exact idx_mul (hind ζ') h)
    change φ _ = 0
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, sub_eq_zero]
    apply ULift.ext
    simp [v, hi, mul_zpow]
  let ψ := (twRel q i B).liftQ φ hker
  constructor
  · intro t t' h
    have h2 := congrArg ψ h
    simp only [LinearMap.map_smul, ψ, Submodule.liftQ_apply, φ, Finsupp.linearCombination_single,
      one_smul] at h2
    have h3 := congrArg ULift.down h2
    change t * (((ind ζ) ^ i : (ZMod q)ˣ) : ZMod q) = t' * (((ind ζ) ^ i : (ZMod q)ˣ) : ZMod q) at h3
    exact (Units.mul_left_inj _).1 h3
  · intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    induction x using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add f g hf hg =>
      obtain ⟨a, ha⟩ := hf
      obtain ⟨b, hb⟩ := hg
      refine ⟨a + b, ?_⟩
      simp only at ha hb ⊢
      rw [Submodule.Quotient.mk_add, ← ha, ← hb, ← add_smul]
      rfl
    | single ξ c =>
      have hmem : Finsupp.single ξ 1 - Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) ∈
          twRel q i B := Submodule.subset_span ⟨ζ, ξ, ind ξ, hind ξ, rfl⟩
      have he : (Submodule.Quotient.mk (Finsupp.single ξ 1) : _ ⧸ twRel q i B) =
          Submodule.Quotient.mk (Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q))) :=
        (Submodule.Quotient.eq _).2 hmem
      refine ⟨(c * ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)).down, ?_⟩
      have hs : Finsupp.single ζ (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) =
          (ULift.up (((ind ξ) ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
        rw [Finsupp.smul_single_one]
      simp only [ULift.up_down]
      rw [← Finsupp.smul_single_one ξ c, Submodule.Quotient.mk_smul, he, hs, Submodule.Quotient.mk_smul, smul_smul]

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.SecSHPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.SecSHPf

theorem bij_of_top (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (hU : ∀ S ∈ Scheme.etaleTopology U, S (𝟙 U)) : Function.Bijective (ofRings.sec (R := R) M U) := by
  constructor
  · intro x y hxy
    have h := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M))
      (X := op U) x y hxy
    have := hU _ h
    simp [Presheaf.equalizerSieve] at this
    exact this
  · intro s
    have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) s
    obtain ⟨t, ht⟩ := hU _ h
    refine ⟨t, ?_⟩
    simp at ht
    exact ht

def ShSect : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)),
  Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _

theorem top_of_sect (hs : ShSect) (A : Type) [CommRing A] (hA : SH A) :
    ∀ S ∈ Scheme.etaleTopology (Spec (CommRingCat.of A)), S (𝟙 _) := by
  intro S hS
  obtain ⟨hH, hsc⟩ := hA
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀).1
    (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))
  have he : Etale (𝒰.f i) := 𝒰.map_prop i
  have hsurj : Surjective (𝒰.f i) := by
    refine ⟨fun p => ?_⟩
    have hsp : p ⤳ (𝒰.f i) y := by
      rw [hy]; exact IsLocalRing.specializes_closedPoint (R := A) p
    obtain ⟨y', -, hy'⟩ := Flat.generalizingMap (𝒰.f i) hsp
    exact ⟨y', hy'⟩
  obtain ⟨s, hs'⟩ := hs A ⟨hH, hsc⟩ _ (𝒰.f i) he hsurj
  have := S.downward_closed (hle (𝒰.X i) (𝒰.f i) (Presieve.ofArrows.mk i)) s
  rwa [hs'] at this

end LateralTheory.KummerTheory.SecSHPf

namespace LateralTheory.KummerTheory

theorem SecSH_of (h : SecSHPf.ShSect) : SecSH := by
  intro A _ hA R _ M
  exact SecSHPf.bij_of_top R M _ (SecSHPf.top_of_sect h A hA)

end LateralTheory.KummerTheory
end
end

