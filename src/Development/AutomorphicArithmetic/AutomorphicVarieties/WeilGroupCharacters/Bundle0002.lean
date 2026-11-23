module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0042

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamFactor
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

private theorem a_mu (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : Subgroup G) (d : ℕ) (A : LocAb l G I d) (g : G) (hg : g ∈ muG l G) : A.a g = 1 := by
  have hc : (commutator G).topologicalClosure ≤ A.a.ker := by
    apply Subgroup.topologicalClosure_minimal
    · exact Abelianization.commutator_subset_ker A.a
    · exact (isClosed_singleton.preimage A.cont : IsClosed (A.a ⁻¹' {1}))
  obtain ⟨n, hn⟩ := CommGroup.mem_primaryComponent.mp hg
  have hpow : g ^ (l ^ n) ∈ (commutator G).topologicalClosure := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hn
    exact hn
  have h1 : A.a g ^ (l ^ n) = 1 := by
    rw [← map_pow]
    exact hc hpow
  have hx : (l ^ n) • Multiplicative.toAdd (A.a g) = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa [toAdd_pow] using this
  have hl : l ^ n ≠ 0 := pow_ne_zero n (Fact.out : l.Prime).ne_zero
  rcases smul_eq_zero.mp hx with h | h
  · exact absurd h hl
  · have e : A.a g = Multiplicative.ofAdd (Multiplicative.toAdd (A.a g)) := rfl
    rw [e, h]
    rfl

private theorem factor (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (I : Subgroup G) (d : ℕ) (A : LocAb l G I d) (R : Type) [CommRing R] (m : Ideal R)
    [IsHausdorff m R] (hl : (l : R) ∈ m) (δ : G →* Rˣ) (hc : AdicCont m fun g => ((δ g : Rˣ) : R))
    (hr : ∀ g, ((δ g : Rˣ) : R) - 1 ∈ m) (hm : ∀ g ∈ muG l G, δ g = 1) :
    ∃ χ : Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]) →* Rˣ, AdicCont m (fun x => ((χ x : Rˣ) : R)) ∧
      ∀ g, χ (A.a g) = δ g := by
  classical
  have key : ∀ x : R, x - 1 ∈ m → ∀ k : ℕ, x ^ (l ^ k) - 1 ∈ m ^ (k + 1) := by
    intro x hx k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have hy : x ^ (l ^ k) - 1 ∈ m := Ideal.pow_le_self (Nat.succ_ne_zero k) ih
      have h1 : Ideal.Quotient.mk m (x ^ (l ^ k)) = 1 := by
        rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk m), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact hy
      have hS : (∑ i ∈ Finset.range l, (x ^ (l ^ k)) ^ i) ∈ m := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        rw [← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]
        exact hl
      have e : x ^ (l ^ (k + 1)) - 1 = (∑ i ∈ Finset.range l, (x ^ (l ^ k)) ^ i) * (x ^ (l ^ k) - 1) := by
        rw [geom_sum_mul, ← pow_mul, ← pow_succ]
      rw [e, pow_succ' m (k + 1)]
      exact Ideal.mul_mem_mul hS ih
  have hk : ∀ g, A.a g = 1 → ∀ N : ℕ, ((δ g : Rˣ) : R) - 1 ∈ m ^ N := by
    intro g hg N
    let ρ : G →* (R ⧸ m ^ N)ˣ := (Units.map (Ideal.Quotient.mk (m ^ N)).toMonoidHom).comp δ
    have hρ : ∀ g, ρ g = 1 ↔ ((δ g : Rˣ) : R) - 1 ∈ m ^ N := by
      intro g
      rw [Units.ext_iff]
      show Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R) = 1 ↔ _
      rw [← map_one (Ideal.Quotient.mk (m ^ N)), Ideal.Quotient.eq]
    have hko : IsOpen (ρ.ker : Set G) := by
      have e : (ρ.ker : Set G) = (fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' {1} := by
        ext g
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
        exact Units.ext_iff
      rw [e]
      exact hc N {1}
    have hopen : IsOpen (ρ.rangeRestrict.ker : Set G) := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hko
    haveI : Finite ρ.range := by
      haveI := Subgroup.quotient_finite_of_isOpen ρ.ker hko
      exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    have hp : IsPGroup l ρ.range := by
      rintro ⟨_, g', rfl⟩
      refine ⟨N, ?_⟩
      apply Subtype.ext
      show ρ g' ^ l ^ N = 1
      rw [← map_pow, hρ, map_pow, Units.val_pow_eq_pow_val]
      exact Ideal.pow_le_pow_right (Nat.le_succ N) (key _ (hr g') N)
    have hmu : muG l G ≤ ρ.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      intro g' hg'
      rw [MonoidHom.mem_ker]
      show Units.map (Ideal.Quotient.mk (m ^ N)).toMonoidHom (δ g') = 1
      rw [hm g' hg', map_one]
    have := A.univ ρ.range hp ρ.rangeRestrict hopen hmu (MonoidHom.mem_ker.mpr hg)
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hρ] at this
    exact this
  have hδ1 : ∀ g, A.a g = 1 → δ g = 1 := by
    intro g hg
    apply Units.ext
    have h0 := IsHausdorff.haus' (I := m) (((δ g : Rˣ) : R) - 1) (fun N => by
      rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
      exact hk g hg N)
    exact sub_eq_zero.mp h0
  let e := QuotientGroup.quotientKerEquivOfSurjective A.a A.surj
  let χ0 : G ⧸ A.a.ker →* Rˣ := QuotientGroup.lift A.a.ker δ
    (fun g hg => MonoidHom.mem_ker.mpr (hδ1 g (MonoidHom.mem_ker.mp hg)))
  let χ := χ0.comp e.symm.toMonoidHom
  have hχ : ∀ g, χ (A.a g) = δ g := by
    intro g
    have h' : e.symm (A.a g) = (g : G ⧸ A.a.ker) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    show χ0 (e.symm (A.a g)) = δ g
    rw [h']
    rfl
  refine ⟨χ, ?_, hχ⟩
  intro N s
  have hcl : IsClosed (A.a '' ((fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' s)ᶜ) :=
    A.cont.isClosedMap _ (hc N s).isClosed_compl
  have heq : ((fun x => Ideal.Quotient.mk (m ^ N) ((χ x : Rˣ) : R)) ⁻¹' s)ᶜ =
      A.a '' ((fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' s)ᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := A.surj x
      exact ⟨g, by simpa [hχ] using hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      simpa [hχ] using hg
  rw [← heq] at hcl
  exact isClosed_compl_iff.mp hcl

theorem UpperTheory.V.W.lam_factor :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) (d : F.Vl → ℕ) (A : ∀ v, LocAb l (F.Gv v) (F.Iv v) (d v)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (v : F.Vl) (i : Fin n) (ψ₀ : F.Gv v →* Rˣ), r.IsPsi v i ψ₀ → ∀ ψ : F.Gv v →* Rˣ,
      r.IsPsi v i ψ ↔ ∃ χ : Multiplicative ((Fin (d v) → ℤ_[l]) × ℤ_[l]) →* Rˣ, AdicCont (maximalIdeal R) (fun x => ((χ x : Rˣ) : R)) ∧ (∀ x, res O R (χ x) = 1) ∧ ψ = ψ₀ * χ.comp (A v).a := by
  intro l _ F O _ _ _ _ _ _ _ n r d A R _ _ _ v i ψ₀ h0 ψ
  haveI hcomp : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hl : (l : R) ∈ maximalIdeal R := by
    rw [← res_eq_zero_iff O R, map_natCast, CharP.cast_eq_zero]
  constructor
  · intro hψ
    let δ : F.Gv v →* Rˣ := ψ * ψ₀⁻¹
    have hδc : AdicCont (maximalIdeal R) (fun g => ((δ g : Rˣ) : R)) := by
      intro N
      have hinv : ∀ u : Rˣ, Ring.inverse (Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R)) =
          Ideal.Quotient.mk (maximalIdeal R ^ N) ((u⁻¹ : Rˣ) : R) := by
        intro u
        have e : Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R) =
            ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N)).toMonoidHom u : (R ⧸ maximalIdeal R ^ N)ˣ) :
              R ⧸ maximalIdeal R ^ N) := rfl
        rw [e, Ring.inverse_unit]
        rfl
      have h1 := hψ.cont N
      have h2 : IsLocallyConstant (fun g => Ring.inverse
          (Ideal.Quotient.mk (maximalIdeal R ^ N) ((ψ₀ g : Rˣ) : R))) :=
        (h0.cont N).comp (Ring.inverse : R ⧸ maximalIdeal R ^ N → R ⧸ maximalIdeal R ^ N)
      convert h1.mul h2 using 1
      funext g
      simp only [δ, MonoidHom.mul_apply, Units.val_mul, map_mul]
      rw [MonoidHom.inv_apply, (hinv (ψ₀ g)).symm]
      rfl
    have hδr : ∀ g, ((δ g : Rˣ) : R) - 1 ∈ maximalIdeal R := by
      intro g
      rw [← res_eq_zero_iff O R, map_sub, map_one]
      have e3 : res O R ((ψ₀ g : Rˣ) : R) * res O R (((ψ₀ g)⁻¹ : Rˣ) : R) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul]
      rw [hψ.red g, ← h0.red g, e3, sub_self]
    have hδm : ∀ g ∈ muG l (F.Gv v), δ g = 1 := by
      intro g hg
      have e1 := hψ.mu ⟨g, hg⟩
      have e2 := h0.mu ⟨g, hg⟩
      have hh : ψ g = ψ₀ g := Units.ext (e1.trans e2.symm)
      simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply, hh, mul_inv_cancel]
    obtain ⟨χ, hχc, hχ⟩ := factor l (F.Gv v) (F.Iv v) (d v) (A v) R (maximalIdeal R) hl δ hδc hδr hδm
    refine ⟨χ, hχc, ?_, ?_⟩
    · intro x
      obtain ⟨g, rfl⟩ := (A v).surj x
      rw [hχ g]
      have := hδr g
      rw [← res_eq_zero_iff O R, map_sub, map_one, sub_eq_zero] at this
      exact this
    · refine MonoidHom.ext fun g => ?_
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hχ g]
      simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply]
      rw [mul_comm (ψ g), mul_inv_cancel_left]
  · rintro ⟨χ, hχc, hχr, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro N
      have h1 := h0.cont N
      have h2 : IsLocallyConstant (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N)
          ((χ ((A v).a g) : Rˣ) : R)) := (hχc N).comp_continuous (A v).cont
      convert h1.mul h2 using 1
      funext g
      rfl
    · intro g
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, map_mul, hχr, mul_one]
      exact h0.red g
    · intro g
      have ha := a_mu l (F.Gv v) (F.Iv v) (d v) (A v) g g.2
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, ha, map_one, mul_one]
      exact h0.mu g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ResidualDatumInertiaCharactersTrivial
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

private theorem unit_eq_one_of_pow {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (x : kˣ) (m : ℕ)
    (h : x ^ l ^ m = 1) : x = 1 := by
  apply Units.ext
  have h' : ((x : k) - 1) ^ l ^ m = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero m (Fact.out : l.Prime).ne_zero)).mp h')

private theorem mu_pow {l : ℕ} [Fact l.Prime] (F : GFrame l) (v : F.Vl) (g : F.mu v) :
    ∃ m : ℕ, (g : F.Gv v) ^ l ^ m ∈ (commutator (F.Gv v)).topologicalClosure := by
  have hg : (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure (g : F.Gv v)) ∈
      CommGroup.primaryComponent (TopologicalAbelianization (F.Gv v)) l := g.2
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure (g : F.Gv v)) ^ l ^ m = 1 := by
    first
      | exact hg
      | (obtain ⟨m, hm⟩ := hg; exact ⟨m, by rw [← hm]; exact pow_orderOf_eq_one _⟩)
  refine ⟨m, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
  exact hm

theorem UpperTheory.V.W.residualDatum_inertia_characters_trivial :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) (v : F.Vl) (i : Fin n) (g : F.mu v), r.psib v i g = 1 ∧ Units.map (residue O : O →* ResidueField O) (r.th v i g) = 1 := by
  intro l _ F O _ _ _ _ n r v i g
  obtain ⟨m, hm⟩ := mu_pow F v g
  constructor
  · apply unit_eq_one_of_pow l _ m
    rw [← map_pow]
    have hle : (commutator (F.Gv v)).topologicalClosure ≤ (r.psib v i).ker :=
      Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _)
        (Subgroup.isClosed_of_isOpen _ (r.psib_open v i))
    exact hle hm
  · apply unit_eq_one_of_pow l _ m
    rw [← map_pow, ← map_pow, r.th_comm v i (g ^ l ^ m) (by simpa using hm), map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ResidualDiagonalDeterminantIsPolar
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W Polynomial

namespace UpperTheory.V.W

private theorem locConst_of_ker {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    (χ : G →* M) (h : IsOpen (χ.ker : Set G)) : IsLocallyConstant χ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernelCapelliIdentities.locConst_of_ker χ h

private theorem locConst_pi {G M ι : Type} [TopologicalSpace G] [Finite ι] (f : ι → G → M)
    (h : ∀ i, IsLocallyConstant (f i)) : IsLocallyConstant fun g i => f i g := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (h i) x
  exact this.mono fun y hy => funext hy

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (y : MonoidAlgebra A G) : (GDet.ofRep ρ).chi y =
      (Matrix.scalar (Fin n) X - GDet.repAlg ρ A[X] (MonoidAlgebra.mapRingHom G C y)).det := by
  change (GDet.repAlg ρ A[X] _).det = _
  rw [map_sub]
  congr 2
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, h]

private theorem star_single {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (b : R) :
    F.star O R n (MonoidAlgebra.single g b) =
      MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp]

private theorem star_sub {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (x y : MonoidAlgebra R F.G₀) :
    F.star O R n (x - y) = F.star O R n x - F.star O R n y := by
  simp [GFrame.star]

private theorem eps_C {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) (m : ℤ) :
    ((F.eps O R[X] g ^ m : R[X]ˣ) : R[X]) = C ((F.eps O R g ^ m : Rˣ) : R) := by
  have h : F.eps O R[X] g = Units.map (C : R →+* R[X]).toMonoidHom (F.eps O R g) := Units.ext rfl
  rw [h, ← map_zpow]
  rfl

end UpperTheory.V.W

theorem UpperTheory.V.W.residual_diagonal_determinant_isPolar :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) [IsCO O (ResidueField O)], 1 ≤ n → r.Ok → ∃ p : Pair r (ResidueField O), p.D = r.Dbar ∧ p.ψ = r.psib := by
  intro l _ F O _ _ _ _ _ _ _ n r _ hn hok
  have hres : ∀ x, res O (ResidueField O) x = x := fun x => by
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact (res O (ResidueField O)).commutes a
  have hres' : (res O (ResidueField O) : ResidueField O →+* ResidueField O) = RingHom.id _ := RingHom.ext hres
  refine ⟨⟨r.Dbar, r.psib, fun i N => ?_, ?_, fun v i => ⟨fun N => ?_, fun g => hres _, fun g => ?_⟩, fun i g => ?_,
    hok.1, fun u g hg h => ?_⟩, rfl, rfl⟩
  · have h1 := locConst_pi _ fun j => locConst_of_ker _ (r.chib_open j)
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ((IsLocallyConstant.iff_eventually_eq _).1 h1 x).mono fun y hy => ?_
    have h2 : diagRep r.chib y = diagRep r.chib x := by
      change Matrix.diagonal _ = Matrix.diagonal _
      congr 1
      funext j
      rw [congrFun hy j]
    simp only [Resid.Dbar, GDet.lam, chi_ofRep]
    simp [GDet.repAlg, h2]
  · rw [hres']
    rfl
  · exact (locConst_of_ker _ (r.psib_open v i)).comp fun u => Ideal.Quotient.mk _ (u : ResidueField O)
  · rw [hok.2 v i g]
    rfl
  · have h1 := r.polar (ResidueField O)[X] (MonoidAlgebra.single 1 X -
      MonoidAlgebra.mapRingHom _ C (MonoidAlgebra.single g (1 : ResidueField O)))
    simp only [GDet.lam, GDet.chi, Resid.Dbar]
    rw [← h1, star_sub]
    simp only [MonoidAlgebra.mapRingHom_single, star_single, eps_C]
    simp
  · have h2 : diagRep r.chib g = 1 := by
      change Matrix.diagonal _ = Matrix.diagonal _
      congr 1
      funext j
      have h3 : r.chib j g = 1 := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2) j
      rw [h3]
      rfl
    have h4 : GDet.repAlg (diagRep r.chib) (ResidueField O)[X] (MonoidAlgebra.mapRingHom _ C
        (MonoidAlgebra.single h (1 : ResidueField O) * (MonoidAlgebra.single g 1 - 1))) = 0 := by
      rw [map_mul, map_mul, map_sub, map_sub, map_one, map_one]
      simp [GDet.repAlg, h2]
    simp only [GDet.tr, Resid.Dbar, GDet.lam, chi_ofRep, h4, sub_zero]
    have h5 : n - 1 ≠ n := by omega
    simp [Matrix.scalar_apply, coeff_X_pow, h5]
end

