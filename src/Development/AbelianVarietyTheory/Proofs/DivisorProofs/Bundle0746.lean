module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharIsCuspidalOfMinpolyOfParam
section
noncomputable section

namespace GlobalTheory.ParamLabel

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.GLq GlobalTheory.GoodCharsCompare GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

variable {p : ℕ} [Fact p.Prime]

theorem isCusp_psi (θ : Fbar p →* ℂ) (hθ : ∀ x y : Fbar p, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) {d k : ℕ} (hd : 0 < d)
    (hk : ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card (ZMod p) ^ i ≡ k [MOD Nat.card (ZMod p) ^ d - 1]) :
    IsCusp (fun x : Gn p d => (-1) ^ (d - 1) *
      psi (rootSum θ k) (Fin d → ZMod p) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod p)))) := by
  classical
  obtain ⟨hch, hip⟩ := GlobalTheory.T.isCharacter_cuspidal_rootSum_regular (ZMod p) θ hθ d k hd hk
  have hadd := (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one (ZMod p) θ k).1
  refine ⟨hd, ?_, fun a ha had => ?_⟩
  · have hs := _root_.GlobalTheory.CuspGL.star_virt_eq_inv _ _ (AddSubgroup.subset_closure (k := {χ | BI.IsChar ℂ ℂ χ}) hch)
    obtain ⟨n, ρ, hρ⟩ := hch
    have hρ' : ∀ x, (FDRep.of ρ).character x = (-1) ^ (d - 1) *
      psi (rootSum θ k) (Fin d → ZMod p) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod p))) :=
      fun x => (hρ x).symm
    refine ⟨FDRep.of ρ, ?_, hρ'⟩
    rw [FDRep.simple_iff_char_is_norm_one]
    rw [(_root_.GlobalTheory.CuspGL.extZero_spec (ZMod p) d (fun _ => 0)).2.2.1, finsum_eq_sum_of_fintype, glCard] at hip
    rw [← hip]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : ((-1 : ℂ) ^ (d - 1)) * ((-1 : ℂ) ^ (d - 1)) = 1 := by
      rw [← mul_pow]; simp
    rw [hρ', hρ', ← hs x, star_mul', star_pow, star_neg, star_one, mul_mul_mul_comm, h1, one_mul]
  · have h := GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive (ZMod p) d _ (_root_.GlobalTheory.CuspGL.isPrimitive_psi (ZMod p) (Fin d → ZMod p) _ hadd) a ha had
    rw [finsum_mem_def, finsum_eq_sum_of_fintype] at h
    have h2 := congrArg (fun z : ℂ => (-1 : ℂ) ^ (d - 1) * z) h
    simp only [mul_zero, Finset.mul_sum] at h2
    unfold res
    refine mul_eq_zero_of_right _ (Eq.trans ?_ h2)
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ (Formalism.D.Classical.grUnipBlock d a : Set (GL (Fin d) (ZMod p)))
    · rw [if_pos ((GlobalTheory.GreenExists.mem_grUnipBlock_iff had u).1 hu), Set.indicator_of_mem (by exact hu)]
    · rw [if_neg (mt (GlobalTheory.GreenExists.mem_grUnipBlock_iff had u).2 hu), Set.indicator_of_notMem (by exact hu), mul_zero]

theorem thetaOf_gen (L : LabelDatum p) {d : ℕ} (hd : 0 < d) (k : ℕ) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    thetaOf L d (L.gen d ^ k) z = L.teich z ^ k := by
  have hp : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  haveI : NeZero (p ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨n, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hz
  rw [Model.thetaOf_gen_pow L hd (by rw [← pow_mul, mul_comm, pow_mul, hp.pow_eq_one, one_pow]),
    ← map_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm]

theorem torVal_eq {d : ℕ} (hd : 0 < d) (θ : Tor p d →* ℂˣ) (F : Fbar p → ℂ)
    (h : ∀ u : Tor p d, ((θ u : ℂˣ) : ℂ) = F ((u : (Fbar p)ˣ) : Fbar p)) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    torVal θ z = F z := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (g_pow_sub_pos hd).ne'] at hz
    exact zero_ne_one hz
  let u : Tor p d := ⟨Units.mk0 z hz0, (mem_rootsOfUnity _ _).2 (Units.ext (by simpa using hz))⟩
  have hinj : Function.Injective (fun u : Tor p d => ((u : (Fbar p)ˣ) : Fbar p)) :=
    fun a b e => Subtype.ext (Units.ext e)
  exact (hinj.extend_apply (fun u => ((θ u : ℂˣ) : ℂ)) 0 u).trans (h u)

theorem cuspOn_eq_psi {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι) {ω : Fbar p →*₀ ℂ}
    (hω : Function.Injective ω) (θ : Tor p (Fintype.card ι) →* ℂˣ) (k : ℕ)
    (h : ∀ u : Tor p (Fintype.card ι), ((θ u : ℂˣ) : ℂ) = ω ((u : (Fbar p)ˣ) : Fbar p) ^ k) :
    cuspOn θ = fun y : Gn p (Fintype.card ι) => (-1) ^ (Fintype.card ι - 1) *
      psi (rootSum (ω : Fbar p →* ℂ) k) (Fin (Fintype.card ι) → ZMod p) (Matrix.toLin' y.val) := by
  classical
  funext y
  obtain ⟨x, hx, hx'⟩ := exists_preimage hω hd (z := rootC (p ^ Fintype.card ι - 1) ^ k)
    (by rw [← pow_mul, mul_comm, pow_mul, (rootC_prim (g := p) hd).pow_eq_one, one_pow])
  have hM : (y.val.submatrix (Fintype.equivFin ι) (Fintype.equivFin ι)).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self]
    exact y.det_ne_zero
  have e1 : cuspOn θ y = cuspVal ω x (y.val.submatrix (Fintype.equivFin ι) (Fintype.equivFin ι)) := by
    unfold cuspOn cuspChar cuspVal
    split_ifs with hh
    · obtain ⟨q, m, hq, hm⟩ := hh
      congr 1
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz1 := root_pow hM hq hm (y := z) (Multiset.mem_toFinset.1 hz)
      obtain ⟨a, ha⟩ := exists_log ω hd hz1
      rw [torVal_eq hd θ (fun z => ω z ^ k) h hz1, labelChar_eq ω hd hx ha, hx', ha, ← pow_mul, ← pow_mul,
        mul_comm a k]
      rfl
    · rfl
  rw [e1, GlobalTheory.CuspFormula.cuspVal_eq_psi ω hd hx hx' _ hM,
    ← _root_.GlobalTheory.CuspGL.psi_conj _ _ _ _ (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (Fintype.equivFin ι)) (Matrix.toLin' y.val)]
  congr 2
  refine LinearMap.ext fun v => ?_
  show Matrix.toLin' (Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm y.val) v = _
  rw [Matrix.toLin'_reindex]
  rfl

theorem isCuspOf_cuspOn (L : LabelDatum p) {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ : Tor p (Fintype.card ι) →* ℂˣ) (x : Fbar p) (hd : 0 < Fintype.card ι) (hL : LabelsChar L θ x)
    (hx : (minpoly (ZMod p) x).natDegree = Fintype.card ι) : IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ) := by
  classical
  obtain ⟨hx1, hθ⟩ := hL
  have hp : IsPrimitiveRoot (L.gen (Fintype.card ι)) (p ^ Fintype.card ι - 1) :=
    L.gen_order _ hd ▸ IsPrimitiveRoot.orderOf _
  haveI : NeZero (p ^ Fintype.card ι - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨k, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hx1
  have hι : Function.Injective (Units.map L.teich) := fun a b e =>
    Units.ext (L.teich_inj _ _ a.ne_zero b.ne_zero (congrArg Units.val e))
  let f : Fbar p → ℂ := fun x => if h : x = 0 then 0 else ((Units.map L.teich (Units.mk0 x h) : ℂˣ) : ℂ)
  have hf0 : ∀ x (hx : x ≠ 0), f x = ((Units.map L.teich (Units.mk0 x hx) : ℂˣ) : ℂ) := fun x hx => dif_neg hx
  have hfz : f 0 = 0 := dif_pos rfl
  let ω : Fbar p →*₀ ℂ :=
    { toFun := f
      map_zero' := hfz
      map_one' := by
        show f 1 = 1
        rw [hf0 1 one_ne_zero, Units.mk0_one, map_one, Units.val_one]
      map_mul' := by
        intro a b
        show f (a * b) = f a * f b
        by_cases ha : a = 0
        · rw [ha, zero_mul, hfz, zero_mul]
        by_cases hb : b = 0
        · rw [hb, mul_zero, hfz, mul_zero]
        rw [hf0 a ha, hf0 b hb, hf0 (a * b) (mul_ne_zero ha hb), Units.mk0_mul, map_mul,
          Units.val_mul] }
  have hω : Function.Injective ω := by
    intro a b hab
    change f a = f b at hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · exfalso
      rw [ha, hfz, hf0 b hb] at hab
      exact Units.ne_zero _ hab.symm
    · exfalso
      rw [hb, hfz, hf0 a ha] at hab
      exact Units.ne_zero _ hab
    · rw [hf0 a ha, hf0 b hb] at hab
      have h := hι (Units.ext hab)
      simpa using congrArg Units.val h
  have he : ∀ u : (Fbar p)ˣ, ((Units.map L.teich u : ℂˣ) : ℂ) = ω u := by
    intro u
    show _ = f u
    rw [hf0 u u.ne_zero, Units.mk0_val]
  have he' : ∀ z : Fbar p, z ^ (p ^ Fintype.card ι - 1) = 1 → L.teich z = ω z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (g_pow_sub_pos hd).ne'] at hz
      exact zero_ne_one hz
    exact he (Units.mk0 z hz0)
  have e := cuspOn_eq_psi hd hω θ k fun u => by
    have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ Fintype.card ι - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
    rw [hθ, thetaOf_gen L hd k hu, he' _ hu]
  have hc : Nat.card (ZMod p) = p := Nat.card_zmod p
  refine ⟨⟨minpoly.monic (isInt _), minpoly.irreducible (isInt _),
    minpoly.coeff_zero_ne_zero (isInt _) (pow_ne_zero _ (hp.ne_zero (g_pow_sub_pos hd).ne')), hx⟩, ?_, ?_⟩
  · rw [e]
    exact isCusp_psi _ (fun _ _ _ _ h => hω h) hd
      (_root_.GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow (ZMod p) _ k (L.gen _) hd (by rw [hc]; exact L.gen_order _ hd) hx)
  · intro x₀ hx₀ y hy z hz
    obtain ⟨j, rfl⟩ := mem_roots_minpoly.1 hx₀
    have hz1 := root_pow y.det_ne_zero hy (pow_one _).symm hz
    rw [Fintype.card_fin] at hz1
    have h := _root_.GlobalTheory.CuspGL.psi_of_irreducible_charpoly (ZMod p) _ _ (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one (ZMod p) (ω : Fbar p →* ℂ) k).1
      (Matrix.toLin' y.val) (by rw [Matrix.charpoly_toLin']; exact hy)
    rw [Matrix.charpoly_toLin'] at h
    rw [e]
    show _ * _ = _
    rw [h]
    congr 1
    change ((Formalism.CyclotomicNorms.rootsBar _).map _).sum = _
    have hnd : y.val.charpoly.natDegree = Fintype.card ι := by simp
    rw [GlobalTheory.GreenExists.rootsBar_eq hy ((mem_rootsBar hy.ne_zero).1 hz), hnd, Multiset.map_map]
    have hs := sum_shift (g := p) (z := ω z) (m := k) (e := Fintype.card ι)
      (by rw [mul_comm, pow_mul, ← map_pow, pow_g_of hz1]) j
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hs.symm.trans (Finset.sum_congr rfl fun i _ => ?_))
    · simp only [Function.comp, MonoidHom.coe_coe, map_pow, ← pow_mul, mul_comm]
    · have hzi : (z ^ p ^ i) ^ (p ^ Fintype.card ι - 1) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
      rw [← pow_mul (L.gen _), thetaOf_gen L hd _ hzi, he' _ hzi, map_pow, ← pow_mul, ← pow_mul]
      congr 1
      ring

theorem isCuspOf_cuspOn_of_green : GlobalTheory.GLq.Green → ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p), 5 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) (x : Fbar p), 0 < Fintype.card ι → LabelsChar L θ x → (minpoly (ZMod p) x).natDegree = Fintype.card ι → GlobalTheory.GLq.IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ) :=
  fun _ _ _ L _ _ _ _ θ x hd hL hx => isCuspOf_cuspOn L θ x hd hL hx

end GlobalTheory.ParamLabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeTransportPreservesSelfDual
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.SeamSelfDual

theorem mem_range_iff {E : Type} [Field E] (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.isIntegral_coe
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem mem_one_iff {E : Type} [Field E] (x : E) :
    x ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one, ← mem_range_iff]
  rfl

theorem isIntegral_map {E E' : Type} [Field E] [Field E'] (f : E →+* E') {x : E}
    (h : IsIntegral ℤ x) : IsIntegral ℤ (f x) :=
  h.map f.toIntAlgHom

theorem isSDLat_pi (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) :
    IsSDLat E n (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := by
  classical
  have hm : ∀ x : Fin n → E, x ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) ↔
      ∀ i, IsIntegral ℤ (x i) := by
    intro x
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, mem_one_iff]
  have hs : ∀ i : Fin n, (Pi.single i 1 : Fin n → E) ∈
      (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
    intro i
    rw [hm]
    intro j
    by_cases h : j = i
    · subst h; simpa using isIntegral_one
    · simpa [Pi.single_apply, h] using isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun hy => ?_⟩⟩
  · rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact hs i
  · rw [mem_range_iff]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => (isIntegral_map (starRingEnd E) (hx i)).mul (hy i)
  · rw [hm]
    intro i
    have := hy _ (hs i)
    rw [mem_range_iff] at this
    have e : stdH E n (Pi.single i 1) y = y i := by
      unfold stdH
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    rwa [e] at this

section Transport

variable {E E' : Type} [Field E] [Field E'] (f : E ≃+* E') {n : ℕ}

theorem isSDLat_image [NumberField E] [NumberField E'] [StarRing E] [StarRing E']
    (hf : ∀ x, f (star x) = star (f x)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsSDLat E n L) :
    IsSDLat E' n (Submodule.span (𝓞 E')
      ((fun (x : Fin n → E) (i : Fin n) => f (x i)) '' (L : Set (Fin n → E)))) := by
  first
  | exact @_root_.GlobalTheory.StandardLatticeSpan.isSDLat_map
  | exact _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map
  | (apply _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StandardLatticeSpan.isSDLat_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map ..)

end Transport

theorem isSDLat_of_isSdLat {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (L : Submodule (𝓞 E) (Sp E n)) (hL : IsSdLat L) : IsSDLat E n L := by
  obtain ⟨h1, h2⟩ := hL
  have hspan : Submodule.span E (L : Set (Sp E n)) = ⊤ := by
    open Formalism.HermitianLatticesTheory in
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v : Sp E n := fun i => star (f (Pi.single i 1))
    have hpair : hStd E n v = f := by
      apply (Pi.basisFun E (Fin n)).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : E) : r • v ∈ L := by
      rw [← show dual (hStd E n) L = L from h2, dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd E n v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd E n y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := E) (n := n)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      let coord := (LinearMap.proj i : Sp E n →ₗ[E] E).restrictScalars (𝓞 E)
      have htop : L.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 E) E := Module.finite_def.mpr (htop ▸ h1.fg.map coord)
      exact RingOfIntegers.not_isField E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  refine ⟨h1.fg, hspan, fun y => ?_⟩
  have h3 : y ∈ L ↔ y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L := by
    rw [show Formalism.HermitianLatticesTheory.dual (hStd E n) L = L from h2]
  rw [h3]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, mem_one_iff, mem_range_iff]
  rfl

theorem seam_selfDual : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → ∀ (n : ℕ), StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) ∧ ∀ L : Submodule (𝓞 X.E) (Sp X.E n), IsSdLat L → StandardLatticesGL3.SD D (s.lat L) := by
  intro D X s hs n
  letI := D.host.cmStar
  refine ⟨isSDLat_pi D.host.E n, fun L hL => ?_⟩
  exact isSDLat_image s.iE (fun x => (hs.2 x).trans (bridge_star_holds D.R D.host _).symm) L
    (isSDLat_of_isSdLat L hL)

end GlobalTheory.SeamSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleClassIdentityComponentIffArtinKernel
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.ArtinKernel

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

theorem eq_one_of_mem_connectedComponent_one (y : GlobalTheory.HeckeGal.Gab K Ω)
    (hy : y ∈ connectedComponent (1 : GlobalTheory.HeckeGal.Gab K Ω)) : y = 1 := by
  by_contra hne
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  let N : Subgroup (Formalism.ConjugateSelfDual.G K Ω) := (commutator (Formalism.ConjugateSelfDual.G K Ω)).topologicalClosure
  have hN : IsClosed (N : Set (Formalism.ConjugateSelfDual.G K Ω)) := Subgroup.isClosed_topologicalClosure _
  have hx : x ∉ N := fun h => hne ((QuotientGroup.eq_one_iff x).2 h)
  have e := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := Formalism.ConjugateSelfDual.G K Ω) ⟨N, hN⟩
  have hx' : x ∉ sInf {M : Subgroup (Formalism.ConjugateSelfDual.G K Ω) | IsOpen (M : Set (Formalism.ConjugateSelfDual.G K Ω)) ∧ N ≤ M} := by
    intro h
    rw [← e] at h
    exact hx h
  rw [Subgroup.mem_sInf] at hx'
  push_neg at hx'
  obtain ⟨M, ⟨hMo, hNM⟩, hxM⟩ := hx'
  let V : Subgroup (GlobalTheory.HeckeGal.Gab K Ω) := M.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (GlobalTheory.HeckeGal.Gab K Ω)) := by
    have : (V : Set (GlobalTheory.HeckeGal.Gab K Ω)) = (QuotientGroup.mk : Formalism.ConjugateSelfDual.G K Ω → _) '' (M : Set _) := by
      rw [Subgroup.coe_map]; rfl
    rw [this]
    exact QuotientGroup.isOpenMap_coe _ hMo
  have hVc : IsClopen (V : Set (GlobalTheory.HeckeGal.Gab K Ω)) := ⟨Subgroup.isClosed_of_isOpen V hVo, hVo⟩
  have hsub := hVc.connectedComponent_subset V.one_mem
  obtain ⟨m, hm, hmx⟩ := hsub hy
  apply hxM
  have : m⁻¹ * x ∈ N := (QuotientGroup.eq).1 hmx
  have := M.mul_mem hm (hNM this)
  simpa using this

theorem mk_mem_connectedComponent_iff {art : Ideles K →* GlobalTheory.HeckeGal.Gab K Ω}
    (h : GlobalTheory.HeckeGal.IsGlobalArtin art) (s : Ideles K) :
    (QuotientGroup.mk s : IdeleClassGroup K) ∈ connectedComponent (1 : IdeleClassGroup K) ↔ art s = 1 := by
  have hker := h.ker
  have hR : (diagUnits K).range ≤ art.ker := by
    rw [hker]; exact le_trans le_sup_left (Subgroup.le_topologicalClosure _)
  let f : IdeleClassGroup K →* GlobalTheory.HeckeGal.Gab K Ω := QuotientGroup.lift _ art hR
  have hf : Continuous f := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr h.quot.continuous
  constructor
  · intro hs
    have := hf.image_connectedComponent_subset (1 : IdeleClassGroup K) ⟨_, hs, rfl⟩
    rw [map_one] at this
    exact eq_one_of_mem_connectedComponent_one _ this
  · intro hs
    have hs' : s ∈ ((diagUnits K).range ⊔ GlobalTheory.HeckeGal.infConn K).topologicalClosure := by
      rw [← hker]; exact hs
    have hC : IsClosed ((QuotientGroup.mk : Ideles K → IdeleClassGroup K) ⁻¹' connectedComponent 1) :=
      isClosed_connectedComponent.preimage continuous_quot_mk
    have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) :=
      Continuous.units_map _ (continuous_id.prodMk continuous_const)
    have hsub : (((diagUnits K).range ⊔ GlobalTheory.HeckeGal.infConn K : Subgroup (Ideles K)) : Set (Ideles K)) ⊆
        (QuotientGroup.mk : Ideles K → IdeleClassGroup K) ⁻¹' connectedComponent 1 := by
      intro y hy
      obtain ⟨a, ⟨k, rfl⟩, b, ⟨c, hc, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hy
      have e : (QuotientGroup.mk (diagUnits K k * Units.map (MonoidHom.inl _ _) c) : IdeleClassGroup K) =
          QuotientGroup.mk (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) c) := by
        refine QuotientGroup.eq.2 ⟨k⁻¹, ?_⟩
        rw [map_inv, mul_inv_rev]
        first
          | exact (inv_mul_cancel_comm _ _).symm
          | (rw [mul_comm, mul_inv_cancel_left])
          | simp [mul_comm, mul_assoc]
      show _ ∈ connectedComponent 1
      rw [e]
      have hg : Continuous (fun c : (InfiniteAdeleRing K)ˣ =>
          (QuotientGroup.mk (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) c) :
            IdeleClassGroup K)) := continuous_quot_mk.comp hinl
      have := hg.image_connectedComponent_subset 1 ⟨c, hc, rfl⟩
      beta_reduce at this
      have h1 : (QuotientGroup.mk (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) 1) :
          IdeleClassGroup K) = 1 := by rw [map_one]; rfl
      rw [h1] at this
      exact this
    have hcl := closure_minimal hsub hC
    rw [← Subgroup.topologicalClosure_coe] at hcl
    exact hcl hs'

theorem idele_class_mem_identity_component_iff :
    ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
      {art : Ideles K →* GlobalTheory.HeckeGal.Gab K Ω}, GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ s : Ideles K,
      (QuotientGroup.mk s : IdeleClassGroup K) ∈ connectedComponent (1 : IdeleClassGroup K) ↔ art s = 1 :=
  fun h s => mk_mem_connectedComponent_iff h s

end GlobalTheory.ArtinKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimesLossLogSumAdmissible
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.InertLossAdm

theorem inertPrimes_loss_log_sum_admissible : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err C := by
  intro eps Fm h0 h1
  obtain ⟨C1, x1, hC1, hc⟩ := GlobalTheory.ConjLossPrimes.loss_sum_primes Fm h0 h1
  obtain ⟨C2, x2, hC2, hi⟩ := GlobalTheory.OtherLoss.inertLoss_primeSum Fm h0 h1
  refine ⟨C1 + C2, max x1 x2, add_nonneg hC1 hC2, ?_⟩
  intro x hx hx1 i j hj P hP
  rw [← Finset.sum_filter_add_sum_filter_not P
    (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)]
  have A := hc x (le_trans (le_max_left _ _) hx) hx1 i j hj (P.filter
    (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0))
    (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨(hP p hp.1).1, (hP p hp.1).2.2⟩)
  have B := hi x (le_trans (le_max_right _ _) hx) hx1 i j hj (P.filter
    (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)))
    (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨(hP p hp.1).1, (hP p hp.1).2.1, (hP p hp.1).2.2, hp.2⟩)
  have eA : ∑ p ∈ P.filter (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0),
      2 * Real.log (p : ℝ) * |Formalism.MainNotions.WeightDegreeSizes.EatCI (Fm.L x i) Fm.GK Fm.cX.err j p| =
      ∑ p ∈ P.filter (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0),
      2 * Real.log (p : ℝ) * |EatC (Fm.L x i) Fm.cX.err j p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    unfold Formalism.MainNotions.WeightDegreeSizes.EatCI
    rw [if_pos hp.2]
  have eB : ∑ p ∈ P.filter (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)),
      2 * Real.log (p : ℝ) * |Formalism.MainNotions.WeightDegreeSizes.EatCI (Fm.L x i) Fm.GK Fm.cX.err j p| =
      ∑ p ∈ P.filter (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)),
      2 * Real.log (p : ℝ) * |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    unfold Formalism.MainNotions.WeightDegreeSizes.EatCI
    rw [if_neg hp.2]
  rw [eA, eB, add_mul]
  exact add_le_add A B

end GlobalTheory.InertLossAdm
end

