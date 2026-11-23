module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HSepOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem exists_separable_aeval_eq_zero_ringOfIntegers {F : Type} [Field F] [NumberField F] {R : Type} [Ring R] [Algebra ℂ R]
    (f : 𝓞 F →+* R) (c : 𝓞 F) : ∃ p : ℂ[X], p.Separable ∧ aeval (f c) p = 0 := by
  have hint : IsIntegral ℤ (c : F) := RingOfIntegers.isIntegral_coe c
  refine ⟨(minpoly ℤ c).map (Int.castRingHom ℂ), ?_, ?_⟩
  · have hq : minpoly ℚ (c : F) = (minpoly ℤ (c : F)).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    have hsep : (minpoly ℚ (c : F)).Separable := Algebra.IsSeparable.isSeparable ℚ (c : F)
    have hm := hsep.map (f := algebraMap ℚ ℂ)
    rw [hq, Polynomial.map_map, RingOfIntegers.minpoly_coe] at hm
    have e : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [e] at hm
    exact hm
  · rw [aeval_def, eval₂_map]
    have e : (algebraMap ℂ R).comp (Int.castRingHom ℂ) = f.comp (algebraMap ℤ (𝓞 F)) :=
      RingHom.ext_int _ _
    rw [e, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

private theorem exists_integral_bezout_of_separable {F : Type} [Field F] [NumberField F] (χ : F[X]) (hs : χ.Separable) :
    ∃ (q u v : (𝓞 F)[X]) (y : ℤ), y ≠ 0 ∧ χ ∣ q.map (algebraMap (𝓞 F) F) ∧
      u * q + v * derivative q = C ((y : 𝓞 F) ^ 2) := by
  classical
  obtain ⟨a, b, hab⟩ := (separable_def' χ).1 hs
  let s : Finset F := (χ.support.image χ.coeff ∪ a.support.image a.coeff) ∪ b.support.image b.coeff
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ s
  have hlift : ∀ P : F[X], (∀ n, P.coeff n ≠ 0 → P.coeff n ∈ s) →
      ∃ Q : (𝓞 F)[X], Q.map (algebraMap (𝓞 F) F) = C (y : F) * P := by
    intro P hP
    have hl : C (y : F) * P ∈ Polynomial.lifts (algebraMap (𝓞 F) F) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_C_mul]
      by_cases h0 : P.coeff n = 0
      · rw [h0, mul_zero]; exact ⟨0, map_zero _⟩
      · have hi := hy _ (hP n h0)
        rw [zsmul_eq_mul] at hi
        obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hi
        exact ⟨z, hz⟩
    exact hl
  have hs1 : ∀ n, χ.coeff n ≠ 0 → χ.coeff n ∈ s := fun n h => by
    simp only [s, Finset.mem_union, Finset.mem_image, Polynomial.mem_support_iff]
    exact Or.inl (Or.inl ⟨n, h, rfl⟩)
  have hs2 : ∀ n, a.coeff n ≠ 0 → a.coeff n ∈ s := fun n h => by
    simp only [s, Finset.mem_union, Finset.mem_image, Polynomial.mem_support_iff]
    exact Or.inl (Or.inr ⟨n, h, rfl⟩)
  have hs3 : ∀ n, b.coeff n ≠ 0 → b.coeff n ∈ s := fun n h => by
    simp only [s, Finset.mem_union, Finset.mem_image, Polynomial.mem_support_iff]
    exact Or.inr ⟨n, h, rfl⟩
  obtain ⟨q, hq⟩ := hlift χ hs1
  obtain ⟨u, hu⟩ := hlift a hs2
  obtain ⟨v, hv⟩ := hlift b hs3
  refine ⟨q, u, v, y, hy0, ?_, ?_⟩
  · rw [hq]; exact dvd_mul_left _ _
  · apply Polynomial.map_injective (algebraMap (𝓞 F) F) RingOfIntegers.coe_injective
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      hq, hu, hv, Polynomial.map_C, Polynomial.derivative_C_mul, map_pow, map_intCast, C_pow]
    simp only [map_intCast, C_eq_intCast]
    linear_combination ((y : F[X])) ^ 2 * hab

private theorem isSemisimple_of_commute_of_integral_bezout {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : R →+* Module.End ℂ V) (hf : ∀ c, (f c).IsSemisimple)
    (h : Module.End ℂ V) (hc : ∀ c, Commute (f c) h) (q u v : R[X]) (y : ℤ) (hy : y ≠ 0)
    (hq : q.eval₂ f h = 0) (huv : u * q + v * derivative q = C ((y : R) ^ 2)) : h.IsSemisimple := by
  classical
  let S : Set (Module.End ℂ V) := Set.range f ∪ {h}
  have hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a (⟨c, rfl⟩ | ha) b (⟨c', rfl⟩ | hb)
    · rw [← map_mul, ← map_mul, mul_comm]
    · rw [Set.mem_singleton_iff.1 hb]; exact hc c
    · rw [Set.mem_singleton_iff.1 ha]; exact (hc c').symm
    · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
  let A := Algebra.adjoin ℂ S
  letI : IsMulCommutative A := Algebra.isMulCommutative_adjoin ℂ (fun a ha b hb _ => hS a ha b hb)
  letI : CommRing A := { (inferInstance : Ring A) with
    mul_comm := isMulCommutative_iff.mp inferInstance }
  have hfA : ∀ c, f c ∈ A := fun c => Algebra.subset_adjoin (Or.inl ⟨c, rfl⟩)
  have hhA : h ∈ A := Algebra.subset_adjoin (Or.inr rfl)
  let fA : R →+* A := f.codRestrict A hfA
  letI : Algebra R A := fA.toAlgebra
  obtain ⟨n, hn, s, hs, hnil, hss, hns⟩ := Module.End.exists_isNilpotent_isSemisimple (f := h)
  have hsub : Algebra.adjoin ℂ {h} ≤ A := Algebra.adjoin_mono Set.subset_union_right
  let x : A := ⟨h, hhA⟩
  let r : A := ⟨s, hsub hs⟩
  have hev : ∀ (z : A) (p : R[X]), ((aeval z p : A) : Module.End ℂ V) = p.eval₂ f (z : Module.End ℂ V) := by
    intro z p
    rw [aeval_def]
    exact Polynomial.hom_eval₂ p (algebraMap R A) (A.val : A →+* Module.End ℂ V) z
  have hx0 : aeval x q = 0 := Subtype.ext (by rw [hev]; exact hq)
  have hunit : IsUnit (aeval x (derivative q)) := by
    have e := congrArg (aeval x) huv
    rw [map_add (f := _), map_mul, map_mul, hx0, mul_zero, zero_add, aeval_C] at e
    have hu : IsUnit (algebraMap R A ((y : R) ^ 2)) := by
      rw [map_pow, map_intCast, ← map_intCast (algebraMap ℂ A)]
      exact (IsUnit.map _ (isUnit_iff_ne_zero.2 (by exact_mod_cast hy))).pow 2
    rw [← e] at hu
    exact isUnit_of_mul_isUnit_right hu
  obtain ⟨r0, -, huniq⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero
    (by rw [hx0]; exact IsNilpotent.zero) hunit
  have hxr : IsNilpotent (x - r) := by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, Subtype.ext ?_⟩
    have e1 : ((x - r : A) : Module.End ℂ V) = n := by
      show h - s = n
      rw [hns]; abel
    rw [SubmonoidClass.coe_pow, e1, hk]
    rfl
  have hsc : ∀ c, Commute (f c) s := fun c =>
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs (hc c)
  have hcomA : ∀ a b : A, Commute (a : Module.End ℂ V) b := fun a b =>
    congrArg Subtype.val (mul_comm a b)
  have hssq : ∀ p : R[X], (p.eval₂ f s).IsSemisimple := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p p' hp hp' =>
      rw [eval₂_add]
      have e1 := hev r p
      have e2 := hev r p'
      refine Module.End.IsSemisimple.add_of_commute ?_ hp hp'
      rw [← e1, ← e2]
      exact hcomA _ _
    | monomial k c =>
      rw [eval₂_monomial]
      exact Module.End.IsSemisimple.mul_of_commute ((hsc c).pow_right k) (hf c) (hss.pow k)
  have hr0 : aeval r q = 0 := by
    have hnil2 := isNilpotent_aeval_sub_of_isNilpotent_sub q hxr
    rw [hx0, zero_sub, isNilpotent_neg_iff] at hnil2
    apply Subtype.ext
    have hnilE : IsNilpotent (q.eval₂ f s) := by
      rw [← hev r q]
      exact hnil2.map (A.val : A →+* Module.End ℂ V)
    rw [hev r q, Module.End.eq_zero_of_isNilpotent_isSemisimple hnilE (hssq q)]
    rfl
  have hxr' : x = r := (huniq x ⟨by simp, hx0⟩).trans (huniq r ⟨hxr, hr0⟩).symm
  have hhs : h = s := congrArg Subtype.val hxr'
  rw [hhs]
  exact hss

theorem UpperTheory.Gal.W2.hSep_of :
    UpperTheory.Gal.W2.HSep := by
  intro F _ _ O _ bar g ρ a H hcomm χ hmon hsep hkill
  obtain ⟨q, u, v, y, hy, hdvd, huv⟩ := exists_integral_bezout_of_separable χ hsep
  let e := Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)
  let f : 𝓞 F →+* Module.End ℂ (Fin g → ℂ) := (e : Matrix (Fin g) (Fin g) ℂ →+* _).comp (ρ.comp a)
  have hf : ∀ c, (f c).IsSemisimple := by
    intro c
    obtain ⟨p, hp, hpa⟩ := exists_separable_aeval_eq_zero_ringOfIntegers f c
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp.squarefree hpa
  have hc : ∀ c, Commute (f c) (e H) := fun c => by
    show e (ρ (a c)) * e H = e H * e (ρ (a c))
    rw [← map_mul, ← map_mul, hcomm c]
  have hq : q.eval₂ f (e H) = 0 := by
    have hk := hkill q hdvd
    rw [eval₂_eq_sum]
    have e2 : (q.sum fun i b => f b * (e H) ^ i) = e (q.sum fun i b => ρ (a b) * H ^ i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Polynomial.sum, map_sum, map_mul, map_pow]
      rfl
    rw [e2, hk, map_zero]
  have hss := isSemisimple_of_commute_of_integral_bezout f hf (e H) hc q u v y hy hq huv
  refine ⟨minpoly ℂ H, ?_, minpoly.aeval ℂ H⟩
  rw [← minpoly.algEquiv_eq e H]
  exact PerfectField.separable_iff_squarefree.mpr hss.minpoly_squarefree
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCspDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem sep_kill {F : Type} [Field F] [NumberField F] {g : ℕ}
    (f : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F) :
    ∃ p : ℂ[X], p.Separable ∧ aeval (f c) p = 0 := by
  have hintF : IsIntegral ℤ (c : F) := NumberField.RingOfIntegers.isIntegral_coe c
  refine ⟨(minpoly ℤ c).map (algebraMap ℤ ℂ), ?_, ?_⟩
  · have h1 : minpoly ℚ (c : F) = (minpoly ℤ (c : F)).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintF
    have h2 : (minpoly ℚ (c : F)).Separable :=
      (minpoly.irreducible (hintF.tower_top (A := ℚ))).separable
    have h3 := h2.map (f := algebraMap ℚ ℂ)
    rw [h1, Polynomial.map_map, NumberField.RingOfIntegers.minpoly_coe] at h3
    have h4 : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = algebraMap ℤ ℂ := RingHom.ext_int _ _
    rwa [h4] at h3
  · rw [aeval_map_algebraMap]
    have h := aeval_algHom_apply f.toIntAlgHom c (minpoly ℤ c)
    rw [minpoly.aeval, map_zero] at h
    exact h

private theorem diag_one {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] {g : ℕ}
    (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (hSim : SimDiag) (hExt : ExtendEmb) :
    ∃ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)), IsDiag a ρ 1 Sb ty (fun _ => 1) := by
  obtain ⟨Sb, e, hdet, he⟩ := hSim g (𝓞 F) (fun c => ρ (a c))
    (fun c c' => (Commute.all c c').map (ρ.comp a)) (fun c => sep_kill (ρ.comp (a)) c)
  have hu : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hdet
  have hinj : ∀ x y : Fin g → ℂ, Sb * Matrix.diagonal x = Sb * Matrix.diagonal y → x = y := by
    intro x y h
    have h' : Matrix.diagonal x = Matrix.diagonal y := by
      have := congrArg (fun m => Sb⁻¹ * m) h
      rwa [← _root_.mul_assoc, ← _root_.mul_assoc, Matrix.nonsing_inv_mul _ hu, _root_.one_mul, _root_.one_mul] at this
    exact Matrix.diagonal_injective h'
  have hadd : ∀ c c', e (c + c') = e c + e c' := by
    intro c c'
    apply hinj
    rw [← he, map_add (f := _), map_add (f := _), add_mul, he, he, ← mul_add, Matrix.diagonal_add]
    try rfl
  have hmul : ∀ c c', e (c * c') = e c * e c' := by
    intro c c'
    apply hinj
    rw [← he, map_mul, map_mul, _root_.mul_assoc, he, ← _root_.mul_assoc, he, _root_.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    try rfl
  have hone : e 1 = 1 := by
    apply hinj
    rw [← he, map_one, map_one, _root_.one_mul]
    show Sb = Sb * Matrix.diagonal (fun _ => 1)
    rw [Matrix.diagonal_one, _root_.mul_one]
  have hzero : e 0 = 0 := by
    apply hinj
    rw [← he, map_zero, map_zero, zero_mul]
    show 0 = Sb * Matrix.diagonal (fun _ => 0)
    rw [Matrix.diagonal_zero, mul_zero]
  let φ : Fin g → (𝓞 F →+* ℂ) := fun i =>
    { toFun := fun c => e c i
      map_one' := by rw [hone]; rfl
      map_mul' := fun c c' => by rw [hmul]; rfl
      map_zero' := by rw [hzero]; rfl
      map_add' := fun c c' => by rw [hadd]; rfl }
  choose ty hty using fun i => hExt F (φ i)
  refine ⟨Sb, ty, hdet, ?_, ?_⟩
  · intro c
    have : (fun i => ty i (c : F)) = e c := by
      funext i
      exact (hty i c).symm
    rw [this]
    exact he c
  · simp

theorem UpperTheory.Gal.W2.cspDim_of :
    UpperTheory.Gal.W2.SimDiag → UpperTheory.Gal.W2.ExtendEmb → UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.MarkDiag → UpperTheory.Gal.W2.BallChar → UpperTheory.Gal.W2.CspDim := by
  intro hSim hExt hTC _ hBall F _ _ O _ bar g ρ a n t₀ ε hS D P₀ M₀ hP hM
  obtain ⟨Sb, ty, hD⟩ := diag_one (F := F) ρ a hSim hExt
  have hcard : (evAt ty (fun _ => (1 : ℂ)) t₀).card = 1 := by
    have h := (hTC F O bar g ρ a n t₀ ε hS 1 Sb ty (fun _ => 1) hD t₀).1
    simpa [typeMult] using h
  obtain ⟨mu, hmu⟩ := Multiset.card_eq_one.mp hcard
  let B := Module.finBasis ℂ (Csp bar ρ M₀)
  let co : (Fin (Module.finrank ℂ (Csp bar ρ M₀)) → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ :=
    (Csp bar ρ M₀).subtype ∘ₗ B.equivFun.symm.toLinearMap
  have hco : IsCoordC bar ρ M₀ co := by
    refine ⟨?_, ?_⟩
    · exact (Submodule.injective_subtype _).comp B.equivFun.symm.injective
    · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have hd := (hBall F O bar g ρ a n t₀ ε hS D P₀ M₀ hP hM 1 (by simp) Sb ty (fun _ => 1) hD mu hmu
    _ co hco LinearMap.id (fun b => by simp)).1
  rw [← hd]
  exact ⟨co, hco⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PDiagExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem sep_of_integer {F : Type} [Field F] [NumberField F] {R : Type} [Ring R] [Algebra ℂ R]
    (f : 𝓞 F →+* R) (c : 𝓞 F) : ∃ p : ℂ[X], p.Separable ∧ aeval (f c) p = 0 := by
  have hint : IsIntegral ℤ (c : F) := RingOfIntegers.isIntegral_coe c
  refine ⟨(minpoly ℤ c).map (Int.castRingHom ℂ), ?_, ?_⟩
  · have hq : minpoly ℚ (c : F) = (minpoly ℤ (c : F)).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    have hsep : (minpoly ℚ (c : F)).Separable := Algebra.IsSeparable.isSeparable ℚ (c : F)
    have hm := hsep.map (f := algebraMap ℚ ℂ)
    rw [hq, Polynomial.map_map, RingOfIntegers.minpoly_coe] at hm
    have e : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [e] at hm
    exact hm
  · rw [aeval_def, eval₂_map]
    have e : (algebraMap ℂ R).comp (Int.castRingHom ℂ) = f.comp (algebraMap ℤ (𝓞 F)) :=
      RingHom.ext_int _ _
    rw [e, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

theorem UpperTheory.Gal.W2.diagExists_of :
    UpperTheory.Gal.W2.SimDiag → UpperTheory.Gal.W2.ExtendEmb → UpperTheory.Gal.W2.KillsMat → UpperTheory.Gal.W2.HSep → UpperTheory.Gal.W2.DiagExists := by
  intro hSim hExt hKills hHSep F _ _ O _ bar g ρ a D P₀ hP ga H hH χ hmin hsep
  have hcomm : ∀ c : 𝓞 F, ρ (a c) * H = H * ρ (a c) := by
    intro c
    have hx : ∀ x : D.La, (ρ (a c) * H) *ᵥ P₀ x = (H * ρ (a c)) *ᵥ P₀ x := by
      intro x
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hH x, ← hP.1 (a c) (ga x),
        ← hP.1 (a c) x, ← hH (a c • x), LinearMap.map_smul]
    have hlin := GlobalTheory.PerCoordU.ext_per hP
      (f := ((ρ (a c) * H).mulVecLin).restrictScalars ℝ)
      (f' := ((H * ρ (a c)).mulVecLin).restrictScalars ℝ) (fun x => by simpa using hx x)
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hlin z
    simpa using hz
  obtain ⟨pH, hpHsep, hpH⟩ := hHSep F O bar g ρ a H hcomm χ hmin.1 hsep
    (fun q hq => (hKills F O bar g ρ a D P₀ hP ga H hH q).1 ((hmin.2 q).2 hq))
  obtain ⟨Sb, d, hdet, hM⟩ := hSim g (Option (𝓞 F))
    (fun o => Option.elim o H (fun c => ρ (a c))) (by
      rintro (_ | c) (_ | c')
      · rfl
      · exact (hcomm c').symm
      · exact hcomm c
      · show ρ (a c) * ρ (a c') = ρ (a c') * ρ (a c)
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm]) (by
      rintro (_ | c)
      · exact ⟨pH, hpHsep, hpH⟩
      · exact sep_of_integer (ρ.comp a) c)
  have hU : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hdet
  have hMs : ∀ c : 𝓞 F, ρ (a c) * Sb = Sb * Matrix.diagonal (d (some c)) := fun c => hM (some c)
  have hd : ∀ c : 𝓞 F, Sb⁻¹ * ρ (a c) * Sb = Matrix.diagonal (d (some c)) := by
    intro c
    rw [Matrix.mul_assoc, hMs c, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
  have hent : ∀ (c : 𝓞 F) (i : Fin g), d (some c) i = (Sb⁻¹ * ρ (a c) * Sb) i i := by
    intro c i
    rw [hd c, Matrix.diagonal_apply_eq]
  let φ : Fin g → (𝓞 F →+* ℂ) := fun i =>
    { toFun := fun c => d (some c) i
      map_one' := by
        show d (some 1) i = 1
        rw [hent, map_one, map_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hU, Matrix.one_apply_eq]
      map_mul' := fun c c' => by
        show d (some (c * c')) i = d (some c) i * d (some c') i
        have h1 := hd (c * c')
        have e : Sb⁻¹ * (ρ (a c) * ρ (a c')) * Sb
            = (Sb⁻¹ * ρ (a c) * Sb) * (Sb⁻¹ * ρ (a c') * Sb) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Sb (Sb⁻¹), Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
        rw [map_mul, map_mul, e, hd, hd, Matrix.diagonal_mul_diagonal] at h1
        have h2 := congrFun (congrFun h1 i) i
        simpa using h2.symm
      map_zero' := by
        show d (some 0) i = 0
        rw [hent, map_zero, map_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
      map_add' := fun c c' => by
        show d (some (c + c')) i = d (some c) i + d (some c') i
        rw [hent, hent, hent, map_add (f := _), map_add (f := _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply] }
  have hτ := fun i => hExt F (φ i)
  choose ty hty using hτ
  refine ⟨Sb, ty, d none, ?_⟩
  refine ⟨hdet, fun c => ?_, hM none⟩
  rw [hMs c]
  congr 2
  funext i
  exact hty i c
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEigTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.eigTop_of :
    UpperTheory.Gal.W2.AdExists → UpperTheory.Gal.W2.DiagExists → UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.RootsFull → UpperTheory.Gal.W2.MarkDiag → UpperTheory.Gal.W2.BallChar → UpperTheory.Gal.W2.FibDet → UpperTheory.Gal.W2.FibW → UpperTheory.Gal.W2.EvIntegral → UpperTheory.Gal.W2.EigTop := by
  intro hAd hDg hTy hRf hMk hBc hFd hFw hEv F _ _ O _ bar g ρ a n t₀ ε hSig D P₀ M₀ hP hM ga H hFix χ hMin hdeg hsep d co hco T hT k α hα
  have hH : H.det ≠ 0 := (hAd O bar g ρ D P₀ M₀ hP hM ga H hFix).1
  obtain ⟨Sb, ty, ev, hD⟩ := hDg F O bar g ρ a D P₀ hP ga H hFix.2 χ hMin hsep
  have hcnt := hTy F O bar g ρ a n t₀ ε hSig H Sb ty ev hD
  have hrts := hRf F O bar g ρ a n t₀ ε hSig D P₀ hP ga H hFix.2 Sb ty ev hD χ hMin hdeg
  have hmk := hMk F O bar g ρ a n t₀ ε hSig H Sb ty ev hD
  refine ⟨?_, ?_⟩
  · have h1 : (evAt ty ev t₀).card = 1 := by
      have h := (hcnt t₀).1
      simpa [typeMult] using h
    obtain ⟨m, hm⟩ := Multiset.card_eq_one.1 h1
    exact ⟨m, (hmk m).2 hm⟩
  intro mu hmu
  have hE : evAt ty ev t₀ = {mu} := (hmk mu).1 hmu
  have hev0 : ∀ i, ev i ≠ 0 := by
    intro i h0
    have hdet : H.det * Sb.det = Sb.det * ∏ j, ev j := by
      have h := congrArg Matrix.det hD.2.2
      simpa [Matrix.det_mul, Matrix.det_diagonal] using h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero] at hdet
    exact mul_ne_zero hH hD.1 hdet
  have hr0 : rts χ t₀ = mu ::ₘ (evAt ty ev (ComplexEmbedding.conjugate t₀)).map (starRingEnd ℂ) := by
    rw [hrts t₀]
    unfold evFull
    rw [hE, Multiset.singleton_add]
  have hnd : (rts χ t₀).Nodup := Polynomial.nodup_roots hsep.map
  rw [hr0, Multiset.nodup_cons] at hnd
  have hne : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), (starRingEnd ℂ) r ≠ mu := by
    intro r hr h
    exact hnd.1 (h ▸ Multiset.mem_map_of_mem _ hr)
  have hnz : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), (starRingEnd ℂ) r ≠ 0 := by
    intro r hr
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hr
    exact (_root_.map_ne_zero _).2 (hev0 i)
  have herase : (rts χ t₀).erase mu = (evAt ty ev (ComplexEmbedding.conjugate t₀)).map (starRingEnd ℂ) := by
    rw [hr0, Multiset.erase_cons_head]
  obtain ⟨-, hdetT⟩ := hBc F O bar g ρ a n t₀ ε hSig D P₀ M₀ hP hM H hH Sb ty ev hD mu hE d co hco T hT
  have hT1 : LinearMap.det (1 - T) =
      ((evAt ty ev (ComplexEmbedding.conjugate t₀)).map fun r => 1 - 1 * (mu / (starRingEnd ℂ) r)).prod := by
    have h := hdetT 1
    rwa [one_smul] at h
  have hfac : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), 1 - 1 * (mu / (starRingEnd ℂ) r) ≠ 0 := by
    intro r hr h
    apply hne r hr
    have hs := hnz r hr
    field_simp at h
    linear_combination h
  have hFib := hFd F O bar g ρ a H Sb ty ev hD k α
  have hF1 : LinearMap.det (1 - fibMap H (diagAct a ρ α)) = ∏ s, ∏ i, (1 - ty i (α s : F) * ev i) := by
    have h := hFib 1
    rw [one_smul] at h
    simpa using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr0]
    exact Multiset.mem_cons_self _ _
  · rw [hT1]
    refine Multiset.prod_ne_zero fun h => ?_
    obtain ⟨r, hr, h0⟩ := Multiset.mem_map.1 h
    exact hfac r hr h0
  · rw [hF1]
    refine Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_
    obtain ⟨x, hx⟩ := hα s
    have h := hEv F O bar g ρ a D P₀ hP ga H hFix.2 Sb ty ev hD i x
    rwa [← hx] at h
  · intro t
    have hball : LinearMap.det (1 - t • T) / LinearMap.det (1 - T) = ballW t₀ t χ mu := by
      unfold ballW
      rw [herase, Multiset.map_map, hdetT t, hT1, ← Multiset.prod_map_div]
      congr 1
      refine Multiset.map_congr rfl fun r hr => ?_
      have hs := hnz r hr
      have h1 := hfac r hr
      have h2 : (starRingEnd ℂ) r - mu ≠ 0 := sub_ne_zero.2 (hne r hr)
      simp only [Function.comp_apply]
      rw [div_eq_div_iff h1 h2]
      field_simp
    unfold locW
    rw [hball, hFib t, hF1, map_prod, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    have h := hFw F g n t₀ ε ty ev χ mu hSig.cx hSig.pos hSig.eps (fun τ => (hcnt τ).1) hrts hE (α s : F) t
    rw [← h, map_prod]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PExtendEmb
section
open NumberField

namespace UpperTheory.Gal.W2

theorem extendEmb_of : ExtendEmb := by
  intro F _ _ φ
  have hker : RingHom.ker φ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hn
    rw [Ideal.mem_bot]
    exact_mod_cast hn
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  refine ⟨IsFractionRing.lift (K := F) hinj, fun c => ?_⟩
  exact (IsFractionRing.lift_algebraMap (K := F) hinj c).symm

end UpperTheory.Gal.W2
end

