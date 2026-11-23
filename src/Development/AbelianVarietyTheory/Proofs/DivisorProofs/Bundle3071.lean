module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishAtPlaces
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharpolyLattice

theorem pts_equiv (k : Type) [Field k] [IsAlgClosed k] (B : GlobalTheory.AV.AbVar k) :
    ∃ e : (Over.mk (𝟙 (Sp k)) ⟶ B.X) ≃* B.Pt,
      ∀ (f : B ⟶ B) (q : Over.mk (𝟙 (Sp k)) ⟶ B.X), e (q ≫ f.hom) = e q ≫ f.hom := by
  have hb : Function.Bijective (algebraMap k (AlgebraicClosure k)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsIso (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  haveI : IsIso (spMap (algebraMap k (AlgebraicClosure k))) :=
    inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
  let i : ptOver k (AlgebraicClosure k) ≅ Over.mk (𝟙 (Sp k)) :=
    Over.isoMk (asIso (spMap (algebraMap k (AlgebraicClosure k)))) (Category.comp_id _)
  refine ⟨{ toFun := fun q => i.hom ≫ q
            invFun := fun q => i.inv ≫ q
            left_inv := fun q => by simp
            right_inv := fun q => by simp
            map_mul' := fun q q' => MonObj.comp_mul _ _ _ }, fun f q => ?_⟩
  exact (Category.assoc i.hom q f.hom).symm

theorem charpoly_reduce {R S : Type} [CommRing R] [CommRing S] (π : R →+* S)
    (hπ : Function.Surjective π) (n : R) (hn : π n = 0)
    {N Q : Type} [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    [AddCommGroup Q] [Module S Q] (e : N →+ Q) (he : Function.Surjective e)
    (hsmul : ∀ (r : R) (x : N), e (r • x) = π r • e x) (hk : ∀ x, e x = 0 → ∃ y, x = n • y)
    (g : N →ₗ[R] N) (G : Q →ₗ[S] Q) (hg : ∀ x, e (g x) = G (e x)) :
    ∃ (_ : Module.Free S Q) (_ : Module.Finite S Q),
      LinearMap.charpoly G = (LinearMap.charpoly g).map π := by
  classical
  let b := Module.Free.chooseBasis R N
  have hsum : ∀ c : Module.Free.ChooseBasisIndex R N → R,
      e (∑ i, c i • b i) = ∑ i, π (c i) • e (b i) := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hsmul _ _
  have hli : LinearIndependent S fun i => e (b i) := by
    refine Fintype.linearIndependent_iff.2 fun s hs i => ?_
    choose c hc using fun i => hπ (s i)
    obtain ⟨y, hy⟩ := hk (∑ i, c i • b i) (by rw [hsum]; simpa only [hc] using hs)
    have h := congrArg (fun z => b.repr z i) hy
    simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    rw [← hc, h, map_mul, hn, zero_mul]
  have hsp : ⊤ ≤ Submodule.span S (Set.range fun i => e (b i)) := by
    intro q _
    obtain ⟨x, rfl⟩ := he q
    rw [← b.sum_repr x, hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = e (b i) := fun i => Module.Basis.mk_apply hli hsp i
  refine ⟨Module.Free.of_basis b', Module.Finite.of_basis b', ?_⟩
  haveI := Module.Free.of_basis b'
  haveI := Module.Finite.of_basis b'
  rw [← LinearMap.charpoly_toMatrix G b', ← LinearMap.charpoly_toMatrix g b, ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb', ← hg]
  conv_lhs => rw [← b.sum_repr (g (b j)), hsum]
  simp only [← hb']
  rw [Module.Basis.repr_sum_self]


open GlobalTheory.HTLat in
theorem lev_pow_smul {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime]
    (s : Tate l M) (j n : ℕ) : (((l : ℤ_[l]) ^ j) • s).lev n = s.lev n ^ l ^ j := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl


open GlobalTheory.HTLat in
theorem tate_lev_eq_one_iff (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime]
    (t : GlobalTheory.HTLat.Tate l M) (j : ℕ) :
    t.lev j = 1 ↔ ∃ s : GlobalTheory.HTLat.Tate l M, t = ((l : ℤ_[l]) ^ j) • s := by
  constructor
  · intro ht
    refine ⟨Tate.mk (fun n => t.lev (j + n)) fun n => ⟨by rw [Tate.lev_add_pow, ht], Tate.lev_succ t (j + n)⟩,
      Tate.ext fun n => ?_⟩
    rw [lev_pow_smul, Tate.lev_mk, add_comm, Tate.lev_add_pow]
  · rintro ⟨s, rfl⟩
    rw [lev_pow_smul, Tate.lev_pow]


open GlobalTheory.HTLat in
theorem tate_lev_surj (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (j : ℕ) (x : M)
    (hx : x ^ (l ^ j) = 1) : ∃ t : GlobalTheory.HTLat.Tate l M, t.lev j = x := by
  choose L hL using GlobalTheory.TateFree.exists_pow_eq hc
  let u : ∀ m : ℕ, {y : M // y ^ l ^ (j + m) = 1} := fun m =>
    Nat.rec (motive := fun m => {y : M // y ^ l ^ (j + m) = 1}) ⟨x, hx⟩
      (fun m y => ⟨L (j + m) y.1 y.2, (hL _ _ _).1⟩) m
  have hu : ∀ m, (u (m + 1)).1 ^ l = (u m).1 := fun m => (hL _ _ _).2
  have hu' : ∀ m, (u m).1 ^ l ^ m = x := fun m => by
    induction m with
    | zero => exact pow_one x
    | succ m ih => rw [pow_succ', pow_mul, hu, ih]
  refine ⟨Tate.mk (fun m => (u m).1 ^ l ^ j) fun m => ⟨?_, ?_⟩, hu' j⟩
  · rw [← pow_mul, ← pow_add]
    exact (u m).2
  · rw [← pow_mul, mul_comm, pow_mul, hu]

end GlobalTheory.CharpolyLattice

namespace GlobalTheory.AV.AbVar


open GlobalTheory.CharpolyLattice GlobalTheory.HTLat in
theorem charpoly_eq_lattice_model : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B)
    (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
    ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ B.X),
    (∀ j x y, ev j (x + y) = ev j x * ev j y) →
    (∀ j x, ev j (φ x) = ev j x ≫ f.hom) →
    (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
    (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ B.X), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
    LinearMap.charpoly φ = GlobalTheory.AV.AbVar.charpoly (End.of f) := by
  intro k _ _ B f L _ _ _ φ l hl hlk ev hadd hequi hker him
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨e, he⟩ := pts_equiv k B
  obtain ⟨hfree, hfin, -, hfinV, -⟩ := tl_free_finrank k l hlk B
  have hc : ∀ n : ℕ, Nat.card {x : B.Pt // x ^ (l ^ n) = 1} = l ^ (2 * B.dim * n) := by
    intro n
    rw [card_torsion_pt k B (l ^ n) (by push_cast; exact pow_ne_zero _ hlk), ← pow_mul, mul_comm n]
  let E : ℕ → L →+ Additive B.Pt := fun j =>
    AddMonoidHom.mk' (fun x => Additive.ofMul (e (ev j x))) fun x y => by
      rw [hadd, map_mul]; rfl
  have hE : ∀ j (n : ℕ) x, e (ev j (n • x)) = e (ev j x) ^ n := fun j n x =>
    congrArg Additive.toMul (map_nsmul (E j) n x)
  have key : ∀ j : ℕ, (LinearMap.charpoly φ).map (Int.castRingHom (ZMod (l ^ j))) =
      (LinearMap.charpoly (tend l B (End.of f))).map (PadicInt.toZModPow j) := by
    intro j
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.ne_zero⟩
    let K := (powMonoidHom (l ^ j) : B.Pt →* B.Pt).ker
    have hK : ∀ x : B.Pt, x ∈ K ↔ x ^ (l ^ j) = 1 := fun x => MonoidHom.mem_ker
    letI : Module (ZMod (l ^ j)) (Additive K) := AddCommGroup.zmodModule fun x =>
      congrArg Additive.ofMul (Subtype.ext (by
        change ((Additive.toMul x : K) : B.Pt) ^ (l ^ j) = 1
        exact (hK _).1 (Additive.toMul x).2))
    have hsm : ∀ (c : ZMod (l ^ j)) (q : Additive K), c • q = c.val • q := fun c q => by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      exact Nat.cast_smul_eq_nsmul _ _ _
    have hπ : ((l : ZMod (l ^ j))) ^ j = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    let G0 : Additive K →+ Additive K := AddMonoidHom.mk'
      (fun q => Additive.ofMul ⟨((Additive.toMul q : K) : B.Pt) ≫ f.hom, (hK _).2 (by
        rw [← ptMap_apply, ← map_pow, (hK _).1 (Additive.toMul q).2, map_one])⟩)
      fun q q' => congrArg Additive.ofMul (Subtype.ext (MonObj.mul_comp _ _ _))
    let G : Additive K →ₗ[ZMod (l ^ j)] Additive K := G0.toZModLinearMap (l ^ j)
    let eL : L →+ Additive K := AddMonoidHom.mk'
      (fun x => Additive.ofMul ⟨e (ev j x), (hK _).2 (by
        rw [← hE, (hker j _).2 ⟨x, rfl⟩, map_one])⟩)
      fun x y => congrArg Additive.ofMul (Subtype.ext (by
        change e (ev j (x + y)) = e (ev j x) * e (ev j y)
        rw [hadd, map_mul]))
    let eT : Tate l B.Pt →+ Additive K := AddMonoidHom.mk'
      (fun t => Additive.ofMul ⟨t.lev j, (hK _).2 (t.lev_pow j)⟩) fun s t => rfl
    obtain ⟨_, _, h1⟩ := charpoly_reduce (Int.castRingHom (ZMod (l ^ j))) ZMod.intCast_surjective
      ((l : ℤ) ^ j) (by rw [map_pow, map_natCast, hπ]) eL
      (fun q => by
        obtain ⟨x, hx⟩ := (him j (e.symm (Additive.toMul q : K))).1 (by
          rw [← map_pow, (hK _).1 (Additive.toMul q).2, map_one])
        refine ⟨x, congrArg Additive.ofMul (Subtype.ext ?_)⟩
        change e (ev j x) = _
        rw [hx, MulEquiv.apply_symm_apply]
        rfl)
      (fun r x => by rw [map_zsmul, eq_intCast, Int.cast_smul_eq_zsmul])
      (fun x hx => by
        have h0 : e (ev j x) = 1 := congrArg Subtype.val (congrArg Additive.toMul hx)
        obtain ⟨y, hy⟩ := (hker j x).1 ((map_eq_one_iff e e.injective).1 h0)
        exact ⟨y, by rw [hy, ← Nat.cast_pow, natCast_zsmul]⟩)
      φ G (fun x => congrArg Additive.ofMul (Subtype.ext (by
        change e (ev j (φ x)) = e (ev j x) ≫ f.hom
        rw [hequi, he])))
    obtain ⟨_, _, h2⟩ := charpoly_reduce (PadicInt.toZModPow j) (ZMod.ringHom_surjective _)
      ((l : ℤ_[l]) ^ j) (by rw [map_pow, map_natCast, hπ]) eT
      (fun q => by
        obtain ⟨t, ht⟩ := tate_lev_surj B.Pt l (2 * B.dim) hc j _ ((hK _).1 (Additive.toMul q).2)
        exact ⟨t, congrArg Additive.ofMul (Subtype.ext ht)⟩)
      (fun a t => by
        rw [hsm]
        rfl)
      (fun t ht => by
        obtain ⟨s, hs⟩ := (tate_lev_eq_one_iff B.Pt l t j).1
          (congrArg Subtype.val (congrArg Additive.toMul ht))
        exact ⟨s, hs⟩)
      (tend l B (End.of f)) G (fun t => rfl)
    exact h1.symm.trans h2
  have hT : (charpoly (End.of f)).map (algebraMap ℤ ℤ_[l]) =
      (tend l B (End.of f)).charpoly := by
    apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange]
    have hcomp : (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) = algebraMap ℤ ℚ_[l] :=
      Subsingleton.elim _ _
    rw [hcomp]
    obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k B (End.of f)
    have hQ := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate k l
      hlk B (End.of f) ((charpoly (End.of f)).map (algebraMap ℤ ℚ)) (hm.map _)
      (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
      (fun n => by rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]; simp)
    rw [Polynomial.map_map] at hQ
    have hcompQ : (algebraMap ℚ ℚ_[l]).comp (algebraMap ℤ ℚ) = algebraMap ℤ ℚ_[l] :=
      Subsingleton.elim _ _
    rw [hcompQ] at hQ
    exact hQ
  have hinj : Function.Injective (Polynomial.map (Int.castRingHom ℤ_[l])) :=
    Polynomial.map_injective _ Int.cast_injective
  apply hinj
  rw [show Int.castRingHom ℤ_[l] = algebraMap ℤ ℤ_[l] from RingHom.ext_int _ _, hT]
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have h := congrArg (fun P : Polynomial (ZMod (l ^ n)) => P.coeff i) (key n)
  simpa only [Polynomial.coeff_map, eq_intCast, map_intCast] using h

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourierClassSumsDeeperFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem classSums_deeper : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 8 → Φ.X y) → Q → PadicAlgCl p) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (X₁.M.Z.presheaf.stalk z₁) B) (_ : Module.Finite (X₁.M.Z.presheaf.stalk z₁) B) (_ : Finite (B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B)) (𝔷 : Ideal B), Function.Injective (algebraMap (X₁.M.Z.presheaf.stalk z₁) B) ∧ (∀ b : B, (∀ σ : B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B, σ b = b) → b ∈ Set.range (algebraMap (X₁.M.Z.presheaf.stalk z₁) B)) ∧ 𝔷.IsMaximal ∧ k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod ℤ N (k y)) ∧ Φ.IsTerms W t ∧ Φ.ClassSums (X₁.S.r * X₁.S.N) N y₀ k t B 𝔷 := by
  intro g n F W Z i X₁ p _ z₁ Φ hΦ y₀ N₀
  obtain ⟨N, hN₀, hdvd, Ω₂, _, _, _, _, hcore⟩ := GlobalTheory.T.thetaFourier_classSums_mem_integralClosure_galois g n F W Z i X₁ p z₁ Φ hΦ y₀ N₀
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := GlobalTheory.T.thetaSetup_stalk_noetherian_normal_fractionRing g n F W Z i X₁ z₁
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.T.integralClosure_galois_finite_autGroup_invariants (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ Ω₂
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra
  obtain ⟨𝔷, hmax⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)
  have hext := fun y => _root_.GlobalTheory.ValExt.exists_ext_centred p (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) 𝔷 hinj hfix hmax (Φ.ev y) (Φ.ev_le y) (Φ.ev_lt y)
  choose ev' h1 h2 h3 using hext
  obtain ⟨k, Q, t, f, hk₀, hk, ht, hf, hcs, hgal⟩ := hcore 𝔷 hmax ev' h1 h2 h3
  refine ⟨N, hN₀, hdvd, k, Q, t, (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), inferInstance, inferInstance, inferInstance, hfin, hfinA, 𝔷, hinj, hfix, hmax, hk₀, hk, ht, ev', f, h1, h2, h3, hf, hcs, fun σ hσ => ?_⟩
  obtain ⟨γ, hdet, hN₁, hσf⟩ := hgal σ hσ
  refine ⟨γ, fun c x => ⟨0, ?_⟩, hdet, hN₁, hσf⟩
  have hm : (Φ.mod y₀) = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  rw [smul_zero, add_zero]
  first
  | (rw [hm]; exact map_zsmul γ c x)
  | (simp only [hm]; exact map_zsmul γ c x)
  | exact map_smul γ c x

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsIntegralTermsUnitShift
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.IntTerm

namespace GlobalTheory.GSep.IntTerm

theorem mem_of_psiCoord {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} (D : DegData V I) {χ : D.toPre.X} (hχ : χ ≠ 0)
    {r : V} (h : Formalism.L2.Pj.PsiCoord D.toPre χ r) : r ∈ I := by
  obtain ⟨j, h₁, h₂, e⟩ := h
  obtain ⟨r', hr', e'⟩ := D.psi_pos χ hχ j ⊤ (isAffineOpen_top _) h₁ h₂
  have e₁ : r' = DegPre.toOpen (R := V) ⊤ r := GlobalTheory.PsiCoordLocal.jK_app_inj ⊤ (e'.trans e.symm)
  rw [e₁] at hr'
  have hb := GlobalTheory.PsiCoordLocal.toOpen_top_bijective (R := V)
  obtain ⟨s, hs, es⟩ := (Ideal.mem_map_iff_of_surjective _ hb.2).1 hr'
  rwa [← hb.1 es]

theorem isUnit_of_sub_mem {V : Type} [CommRing V] [IsLocalRing V] {a b : V} (h : a - b ∈ maximalIdeal V) :
    IsUnit a ↔ IsUnit b := by
  rw [← not_iff_not, ← mem_nonunits_iff, ← mem_nonunits_iff, ← mem_maximalIdeal, ← mem_maximalIdeal]
  exact ⟨fun ha => by simpa using sub_mem ha h, fun hb => by simpa using add_mem h hb⟩

theorem exists_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∃ u : X → C → V, 𝔪.Terms x₀ lab (fun mu c => u mu c * t mu) ∧ (∀ mu, ∃ c, IsUnit (u mu c)) ∧ ∀ c, lab c = x₀ → IsUnit (u 0 c) := by
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev X _ t δ 𝔪 C lab hlab
  have hV := 𝔪.cn
  haveI : IsNoetherianRing V := hV.1
  haveI : CharZero V := hV.2.2.2
  have hA := admissibleBase_of_completeNormalLocalCharZero hV
  have hL := GlobalTheory.firstFiveLaws
  have hN₂ : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hN : 1 ≤ X₁.S.r * X₁.S.N := by omega

  have ht0 : IsUnit (t 0) := by
    obtain ⟨u₀, hu₀⟩ := 𝔪.psi 0
    obtain ⟨r₀, hr₀, -, -, hu⟩ := (GlobalTheory.PsiCoordLocal.main V 𝔪.D hV.2.1 (𝔪.e₈ 0)).1
    obtain ⟨v, hv⟩ := (GlobalTheory.PsiCoordLocal.main V 𝔪.D hV.2.1 (𝔪.e₈ 0)).2.1 r₀ _ hr₀ hu₀
    have h1 : IsUnit ((u₀ : V) * t 0) := hv ▸ v.isUnit.mul (hu (map_zero _))
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨x, fr, th, ρ, hx, hfr, hth, hρ, htf⟩ := GlobalTheory.T.exists_points_frames_thetaSection_member I X₁ z₁ act V ev X t δ 𝔪
  obtain ⟨hNu, h0, hdv⟩ := _root_.GlobalTheory.GSep.unit_ne_zero_dvd I X₁ z₁ act V ev X t δ 𝔪 x₀ hdiv
  obtain ⟨w₀, hw₀⟩ := 𝔪.U.ext
  obtain ⟨s, hs, -⟩ := ((expBijF_and_expandsF_lin hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U).1 (FractionRing V) 1 le_rfl w₀ hw₀).1 th
  obtain ⟨l, hl, hlf⟩ := GlobalTheory.T.exists_torsion_frame_eq_const_mul_integral_generator V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ ρ hρ _ hN
  have hint := _root_.GlobalTheory.GSep.mem_HH_iff_yy_zero I X₁ z₁ act x₀ hdiv V ev X t δ 𝔪

  have hxb : ∀ (a) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A),
      xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left →
      xb.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ (x a).left := by
    intro a xb h
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · rw [h, Category.assoc, hx a, ← Category.assoc]
      congr 1
      rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
    · rw [Category.assoc, Over.w, Over.w]
      change _ = _ ≫ Spec.map (𝟙 _)
      rw [Spec.map_id, Category.comp_id]; rfl
  have hyy : ∀ c, 𝔪.YY (lab c) 0 := fun c => (hint _).1 (by
    have : lab c ∈ Set.range lab := ⟨c, rfl⟩
    rwa [hlab] at this)
  choose p xb hp hq hxp using hyy
  have hp0 : ∀ c, (p c).y = 0 := fun c => (hp c).trans (map_zero _)
  choose h gi hh hgt hfe hext hpull using fun c => GlobalTheory.T.rationalTorsionPoint_lift_section_torusExtension V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN (x (lab c)) (xb c) (p c)
    (hxb _ _ (hxp c)) (hp0 c) (hq c)
  choose g' hg' using fun c => GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) (gi c)
  choose w hw hif hlies using fun c => GlobalTheory.T.sectionValue_integralPoint_eq_adicSum_terms V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ (x (lab c)) (fr (lab c)) (h c) (gi c)
    (g' c) l hl (hfe c) (hext c) (hg' c) (hlf _ _ _ (htf _) (hh c) (hext c))
  have htor : ∀ c, ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero := fun c => by
    obtain ⟨o, ho, hz⟩ := hgt c
    obtain ⟨o', ho'⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) o
    exact ⟨o', GlobalTheory.FieldRestrictionTest.isNsmul_restrict (hg' c) ho' ho,
      GlobalTheory.FieldRestrictionTest.isZero_restrict ho' hz⟩
  have hb : ∀ c, (g' c).b = toUnit _ ≫ (gi c).b := fun c =>
    ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hg' c)).1
  have hex : Exhausts 𝔪.D.toPre.P (X₁.S.r * X₁.S.N) fun c => (gi c).b := by
    refine GlobalTheory.T.torsionSections_exhaust_of_generic_geometric V _ _ hN C _ (fun c => (Sep.Frames.torsion_of_nsmul (g' c) _ (hb c) (htor c)).2) fun β hβ => ?_
    obtain ⟨y, hy, ⟨q, hq0, hqy⟩, H⟩ := GlobalTheory.T.geometricTorsionPoint_abelianPart_lies_under_classZero V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN β hβ
    obtain ⟨a, ha⟩ := GlobalTheory.T.geometricTorsionPoint_member_has_label I X₁ z₁ act V ev X t δ 𝔪 y hy
    have hmem : a ∈ Set.range lab := by
      rw [hlab]
      exact (hint a).2 ⟨q, y, hq0.trans (map_zero _).symm, hqy, ha⟩
    obtain ⟨c, rfl⟩ := hmem
    have e : xb c = y := Over.OverMorphism.ext ((hxb _ _ (hxp c)).trans (hxb _ _ ha).symm)
    exact ⟨c, (H (p c) (hp0 c) (e ▸ hq c)).symm.trans ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hpull c)).1⟩
  obtain ⟨θ, hθ⟩ := exists_isTheta hV 𝔪.D.toPre
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.degree_one_term_eq_const_mul_psi_mul_theta V 𝔪.D.toPre θ hθ s
  choose υ hυ using 𝔪.psi
  choose a ha hau using fun mu c => hκ (gi c) (g' c) (w c) l (hg' c) (hw c) (hif c) (𝔪.e₈ mu) _ (hυ mu)
  have hunit : ∀ mu, ∃ c, IsUnit (a mu c) := fun mu =>
    (_root_.GlobalTheory.Poinc.IntTerm.exists_unitAt_mul V 𝔪.D.toPre θ hθ _ hN₂ hNu C _ hex (𝔪.D.toPre.c (𝔪.e₈ mu))).imp fun c hc => hau mu c hc
  have hco : ∀ mu c, coef s (g' c) (w c) (𝔪.e₈ mu) =
      l⁻¹ * κ * algebraMap V (FractionRing V) (υ mu * t mu * a mu c) := fun mu c => by
    rw [_root_.mul_assoc, ← ha, inv_mul_cancel_left₀ hl]
  have hsum : ∀ c, ∃ S : V, 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ = l⁻¹ * κ * algebraMap V (FractionRing V) S ∧
      (IsUnit S ↔ IsUnit (a 0 c)) := fun c => by
    obtain ⟨S, hS, hm⟩ := _root_.GlobalTheory.Poinc.AdicTerm.sumF_mul V _ (𝔪.e₈ 0) (coef s (g' c) (w c))
      (fun χ => υ (𝔪.e₈.symm χ) * t (𝔪.e₈.symm χ) * a (𝔪.e₈.symm χ) c) (l⁻¹ * κ) _
      (fun χ => by rw [← hco, AddEquiv.apply_symm_apply])
      (fun χ hχ => Ideal.mul_mem_right _ _ (mem_of_psiCoord 𝔪.D (χ := 𝔪.e₈ (𝔪.e₈.symm χ))
        (by rwa [AddEquiv.apply_symm_apply, ← map_zero 𝔪.e₈]) (hυ _)))
      (hlies c 1 le_rfl (w c) (fun _ _ _ => (pow_one _).symm) (hw c) th s _ hs (hth _))
    refine ⟨S, hS, (isUnit_of_sub_mem hm).trans ?_⟩
    simp only [AddEquiv.symm_apply_apply]
    rw [_root_.mul_assoc, Units.isUnit_units_mul]
    exact ⟨fun h' => isUnit_of_mul_isUnit_right h', fun h' => ht0.mul h'⟩
  choose S hS hSu using hsum
  have hx₀ : x₀ ∈ Set.range lab := by
    rw [hlab]
    exact AddSubgroup.subset_closure hdiv
  obtain ⟨c₀, rfl⟩ := hx₀
  have hκ0 : l⁻¹ * κ ≠ 0 := left_ne_zero_of_mul (hS c₀ ▸ h0)
  have inj := IsFractionRing.injective V (FractionRing V)
  have hS₀ : IsUnit (S c₀) := by
    obtain ⟨c₁, hc₁⟩ := hunit 0
    obtain ⟨r, hr⟩ := hdv (lab c₁)
    rw [hS, hS, mul_left_comm, ← map_mul] at hr
    have e := inj (mul_left_cancel₀ hκ0 hr)
    exact isUnit_of_mul_isUnit_right (e ▸ (hSu c₁).2 hc₁)
  obtain ⟨σ, hσ⟩ := hS₀
  refine ⟨fun mu c => υ mu * a mu c * σ⁻¹, ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs,
    fun c => ⟨htor c, hw c, hlies c⟩, fun mu c => ?_⟩, fun mu => (hunit mu).imp fun c hc => ?_, fun c hc => ?_⟩
  · rw [hco, hS, ← hσ, mul_left_comm, ← map_mul]
    congr 2
    linear_combination (υ mu * a mu c * t mu : V) * σ.inv_mul
  · exact ((υ mu).isUnit.mul hc).mul (σ⁻¹).isUnit
  · have e₁ := hS c
    have e₂ := hS c₀
    simp only [hc] at e₁
    have e := inj (mul_left_cancel₀ hκ0 (e₁.symm.trans e₂))
    exact ((υ 0).isUnit.mul ((hSu c).1 (e ▸ hσ ▸ σ.isUnit))).mul (σ⁻¹).isUnit

end GlobalTheory.GSep.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorsionFrameUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_torsion_frame_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x)
  (g g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  w₀.IsGen → fr.IsGen →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g w x fr →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀ g₂ w₂ x fr →
  g₂.b = g.b → (∀ χ z J, Good 𝔪.D.toPre.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J) →
  ∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val w (𝟙 _) z J := by
  first | exact @GlobalTheory.GSep.FrameUniq.frame_val_eq | exact GlobalTheory.GSep.FrameUniq.frame_val_eq | (intros; apply GlobalTheory.GSep.FrameUniq.frame_val_eq <;> assumption)
end

