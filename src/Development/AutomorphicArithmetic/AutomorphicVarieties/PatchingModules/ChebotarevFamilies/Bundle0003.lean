module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0016

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.ChebFam
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.chebFam :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (U : Subgroup (G L Ω)) (q : ℕ) (g : Fin q → G L Ω) (A : Set (Plc (Lp L))), IsOpen (U : Set (G L Ω)) → A.Finite → ∃ (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L) (B : Fin q → ValuationSubring Ω) (σ : Fin q → G L Ω), Function.Injective v ∧ ∀ j, v j ∉ A ∧ IsPlaceOver (B j) (w j) ∧ IsPlaceOver (B j) (v j) ∧ Dec (F := Lp L) (B j) ≤ (resP L Ω).range ∧ IsFrob (F := L) (B j) (normV (w j)) (σ j) ∧ σ j * (g j)⁻¹ ∈ U := by
  intro L Ω _ _ _ _ _ _ U q g A hU hA
  revert g
  induction q with
  | zero =>
    intro g
    exact ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun j => j.elim0⟩
  | succ q ih =>
    intro g
    obtain ⟨v, w, B, σ, hinj, hj⟩ := ih (fun i => g i.castSucc)
    obtain ⟨v0, w0, B0, σ0, h1, h2, h3, h4, h5, h6⟩ :=
      chebOne L Ω U (g (Fin.last q)) (A ∪ Set.range v) hU (hA.union (Set.finite_range v))
    refine ⟨fun i => Fin.lastCases v0 v i, fun i => Fin.lastCases w0 w i,
      fun i => Fin.lastCases B0 B i, fun i => Fin.lastCases σ0 σ i, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hij
      · rfl
      · exact (h1 (Or.inr ⟨_, hij.symm⟩)).elim
      · exact (h1 (Or.inr ⟨_, hij⟩)).elim
      · rw [hinj hij]
    · intro j
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        exact ⟨fun h => h1 (Or.inl h), h2, h3, h4, h5, h6⟩
      | cast i =>
        simp only [Fin.lastCases_castSucc]
        exact hj i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PFromAutOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem map_ofRep {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (f : A →+* B) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2

theorem chain_of (hN : Norm) (hC : Choice) (hP : ArPl) (h1 : FirstOrderDualArithmeticBound) (h2 : TaylorWilesObstructionBound) (hR : Raw) (P : CohP)
    (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (hn : 0 < n) (hS : V0.S' = s.S)
    (hL : LocCFT s) (hμ : ∃ g : V0.frame.G₀, PadicInt.toZMod ((V0.frame.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) (hA : HasAut B J)
    (h : ℕ) (x : Fin (h + 1) → Point r) (f : ∀ i, B.B →ₐ[O] (x i).A) (hx : ∀ i, (x i).NiceI ∨ (x i).NiceE)
    (hf : ∀ i, B.IsPt (x i) (f i)) :
    ChainConcl (pairOf B.u) J (fun i => RingHom.ker (f i)) ∧
      ∀ i, (x i).TypeI → ∀ q : Ideal B.B, q ≤ RingHom.ker (f i) → DiscSt B.u.D q := by
  haveI := IsCoef.char (l := l) (O := O)
  haveI := IsCoef.finite (l := l) (O := O)
  haveI := IsCoef.complete (l := l) (O := O)
  obtain ⟨hΦ, hT⟩ := hP P l L Ω s V0 O n r hS
  have hI := (ipEq l L Ω s V0 O n r).1
  choose y j jinj jloc _ jD jψ y3 y4 yI using fun i => hN l V0.frame O n r (x i) (globOf r V0).frame.Iu s.odd hn
    (fun u => ((hI u).2.symm.trans (hI u).1).le) (hx i)
  obtain ⟨q, sg, z, j', k, al, hsg, hE, hcard, hdet, heig⟩ := hC l (globOf r V0).frame n h y s.odd hΦ hμ y3
  obtain ⟨T, ⟨Pl⟩, rfl, hTs⟩ := hT q sg hsg
  obtain rfl : T.sg = sg := funext hTs
  obtain ⟨A⟩ := hA T Pl
  choose ι hι using fun i => Det.constMap ((j' i).comp (j i))
  have hD : ∀ i, GDet.ofRep (mat (z i).ρ) = (GDet.ofRep (mat (x i).ρ)).map ((j' i).comp (j i)) := fun i => by
    exact (Det.coefficientExtension_preserves_conditions_and_det _ _ _ (hE i)).2.2.trans (congrArg (·.map (j' i)) (jD i))
  have hker : ∀ i, ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → (z i).ρ g = 1 := fun i => by
    refine rhoPL l (globOf r V0).frame n (z i) T.H fun g hg => ?_
    obtain ⟨e1, e2, -⟩ := (Pl.H_eq g).1 hg
    refine ⟨e1, ?_⟩
    have hcc : (PowerSeries.constantCoeff : (z i).A →+* (z i).K).comp ((j' i).comp (j i)) =
        (ι i).comp PowerSeries.constantCoeff := RingHom.ext fun a => by
      haveI := jloc i
      haveI := (hE i).2.1
      have m1 : ¬ IsUnit (a - PowerSeries.C (PowerSeries.constantCoeff a)) := by
        simp [PowerSeries.isUnit_iff_constantCoeff]
      have m2 : ¬ IsUnit (j' i (j i (a - PowerSeries.C (PowerSeries.constantCoeff a)))) := fun u =>
        m1 (IsLocalHom.map_nonunit _ (IsLocalHom.map_nonunit _ u))
      rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not, map_sub, map_sub, map_sub, sub_eq_zero] at m2
      have m3 := congrArg PowerSeries.constantCoeff (hι i (PowerSeries.constantCoeff a))
      exact m2.trans (m3.trans (PowerSeries.constantCoeff_C _))
    have e3 : (GDet.ofRep (mat (z i).ρ)).map (PowerSeries.constantCoeff : (z i).A →+* (z i).K) =
        r.Dbar.map ((ι i).comp (algebraMap (ResidueField O) (x i).K)) := by
      rw [hD i]
      refine Eq.trans (b := (GDet.ofRep (mat (x i).ρ)).map ((ι i).comp PowerSeries.constantCoeff)) (by rw [← hcc]; rfl) ?_
      exact congrArg (·.map (ι i)) (x i).red
    rw [map_ofRep, Resid.Dbar, map_ofRep] at e3
    have e4 := congrArg (·.chi (MonoidAlgebra.single ⟨g, e1⟩ 1)) e3
    simp only [chi_ofRep] at e4
    refine e4.trans ?_
    have e5 : W.diagRep r.chib ⟨g, e1⟩ = 1 := by
      change Matrix.diagonal _ = _
      simp only [e2, Units.val_one, Matrix.diagonal_one]
    refine (chi_ofRep _ _).trans ?_
    change ((RingHom.mapMatrix ((ι i).comp (algebraMap (ResidueField O) (x i).K))) (W.diagRep r.chib ⟨g, e1⟩)).charpoly = _
    rw [e5, map_one, Matrix.charpoly_one, Fintype.card_fin]
  let pt : ∀ i, Pt T (pairOf B.u) (n * Module.finrank ℚ (Lp L) + n * T.q) := fun i =>
    letI : Algebra O (z i).K := ((ι i).comp (algebraMap O (x i).K)).toAlgebra
    { x := z i
      k := k i
      al := al i
      eig := heig i
      b1 := h1 P l L Ω s V0 O n r T Pl (z i) (k i) (al i) hS hL hμ (hker i)
        ((Det.coefficientExtension_preserves_conditions_and_det _ _ _ (hE i)).1 _ (y4 i)) (heig i) (hdet i)
      b2 := h2 P l L Ω s V0 O n r T Pl (z i) (k i) (al i) hS hμ (hker i) (heig i)
      f := { ((j' i).comp (j i)).comp (f i : B.B →+* (x i).A) with
        commutes' := fun a => by
          change ((j' i).comp (j i)) (f i (algebraMap O B.B a)) = _
          rw [AlgHom.commutes]
          rw [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply]
          exact hι i _ }
      maps := ⟨by rw [hD i, ← (hf i).1]; rfl, fun v a => by
        rw [(hE i).2.2.2.2.2 v a, jψ i v a, ← (hf i).2 v a]; rfl⟩ }
  have hk : ∀ i, RingHom.ker (pt i).f = RingHom.ker (f i) := fun i => by
    ext b
    change j' i (j i (f i b)) = 0 ↔ f i b = 0
    rw [map_eq_zero_iff _ (hE i).1, map_eq_zero_iff _ (jinj i)]
  refine ⟨?_, fun i hi q hq => ?_⟩
  · have := hR l _ (globOf r V0) T n O (residOf r) B.B (pairOf B.u) J _ A s.odd
      ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩
      (fun N b => by
        obtain ⟨c, hc, hb⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b
        refine ⟨c, Algebra.adjoin_mono ?_ hc, hb⟩
        rintro _ (⟨a, g, -, -, rfl⟩ | e)
        · exact Or.inl ⟨a, g, rfl⟩
        · exact Or.inr e) h pt hcard
    simpa only [hk] using this
  · exact Det.typeIDisc (z i) B.u.D (((j' i).comp (j i)).comp (f i : B.B →+* (x i).A)) ((hE i).2.2.2.2.1.trans (yI i hi)) (pt i).maps.1 q (hq.trans (hk i).ge)

theorem pFromAut_of (hN : Norm) (hC : Choice) (hP : ArPl) (h1 : FirstOrderDualArithmeticBound) (h2 : TaylorWilesObstructionBound) (hR : Raw) : PfromAut := by
  intro P l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J hn hS hL hμ hA
  have key := chain_of hN hC hP h1 h2 hR P l L Ω s V0 O n r B J hn hS hL hμ hA
  have hE : augmentationIdealKernel (pairOf B.u) = augmentationIdealKernel B.u := by
    rw [(ipEq l L Ω s V0 O n r).2 B]
    ext z
    simp only [augmentationIdealKernel, UniversalOrdinaryDeterminantRing.GroupAlgebraKernelIdeal, GDet.chBar, pairGens, UniversalOrdinaryDeterminantRing.E0gens, Set.mem_setOf_eq, Set.union_assoc]
  refine ⟨fun x f hx hf hJ q hq => ?_, fun h x f e hx hf he h₁ q hq hs => ?_⟩
  · obtain ⟨k1, k2⟩ := key 0 (fun _ => x) (fun _ => f) (fun _ => Or.inl hx) fun _ => hf
    exact k1 Fin.elim0 (fun i => i.elim0) ⟨_, RingHom.ker_isPrime f, k2 0 hx.2.1 _ le_rfl, hJ, le_rfl⟩ q.asIdeal q.isPrime hq
      (Or.inl (k2 0 hx.2.1 _ hq))
  · obtain ⟨k1, -⟩ := key h x f (fun i => Or.inr (hx i)) hf
    obtain ⟨q₁, a1, a2, a3⟩ := h₁
    refine k1 (fun i => (e i).asIdeal) (fun i => ⟨(e i).isPrime, hE ▸ Det.thickNonSS B _ (he i).1, (he i).2⟩)
      ⟨_, q₁.isPrime, (Det.stableIff B _).1 a1, a2, a3⟩ q.asIdeal q.isPrime hq ?_
    exact hs.imp (Det.stableIff B _).1 fun t => hE ▸ Det.thickNonSS B _ t

end UpperTheory.V.Pa
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PLNormal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

open scoped Pointwise in
private theorem conj_ine {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, ∀ t ∈ Ine (F := k) B, g⁻¹ * t * g ∈ Ine (F := k) A := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := k) hA hB
  have hm : ∀ x, g x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have hv : ∀ x, B.valuation (g x) < 1 ↔ A.valuation x < 1 := fun x => by
    rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω), hm, ← map_inv₀, hm,
      map_eq_zero_iff _ g.injective]
  refine ⟨g, fun t ht => ⟨?_, fun x hx => ?_⟩⟩
  · show (g⁻¹ * t * g) • A = A
    have h1 : t • B = B := ht.1
    rw [mul_smul, mul_smul, hg, h1, ← hg, inv_smul_smul]
  · rw [← hv, map_sub]
    have e : g ((g⁻¹ * t * g) x) = t (g x) := mul_inv_apply _
    rw [e]
    exact ht.2 _ ((B.valuation_le_one_iff _).2 ((hm x).2 ((A.valuation_le_one_iff _).1 hx)))

open scoped Pointwise in
private theorem res_ine {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (A : ValuationSubring Ω) (g : G L Ω) : resP L Ω g ∈ Ine (F := Lp L) A ↔ g ∈ Ine (F := L) A := Iff.rfl

private theorem ine_NS {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {S : Set (HeightOneSpectrum (𝓞 k))} {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hv : v ∉ S)
    (hA : IsPlaceOver A v) {t : G k Ω} (ht : t ∈ Ine (F := k) A) : toGS Ω S t = 1 := by
  refine (QuotientGroup.eq_one_iff t).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, ht⟩

private theorem PL_normal (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ) : (PL l H).Normal := by
  refine ⟨fun x hx g => ?_⟩
  unfold PL at hx ⊢
  simp only [Subgroup.mem_iInf] at hx ⊢
  intro U hU
  exact U.isNormal'.conj_mem _ (hx U hU) g

theorem UpperTheory.V.Pa.kerLe :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (h : (globOf r V).Hom (globOf r V0)) (H : Subgroup (globOf r V0).Γ) (q : ℕ) (v : Fin q → Plc (Lp L)) (B : Fin q → ValuationSubring Ω) (τ : Fin q → G L Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → V.S' = V0.S' ∪ Set.range v → (∀ j, v j ∉ V0.S' ∧ IsPlaceOver (B j) (v j) ∧ Dec (F := Lp L) (B j) ≤ (resP L Ω).range ∧ GlobalTheory.TameQuot.IsProGen L (B j) l (τ j)) → (∀ j, ∀ g ∈ Ine (F := L) (B j), h.p (V.pr g : GS Ω V.S') = 1) ∧ (∀ j, ∀ g ∈ GlobalTheory.TameQuot.ineKer L (B j) l, ((V.pr g : GS Ω V.S') : (globOf r V).Γ) ∈ PL l (H.comap h.p)) ∧ h.p.ker ≤ (Subgroup.normalClosure (Set.range fun j => ((V.pr (τ j) : GS Ω V.S') : (globOf r V).Γ)) ⊔ PL l (H.comap h.p)).topologicalClosure := by
  intro l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ n r h H q v B τ hp hS hj
  have h1 : ∀ j, ∀ g ∈ Ine (F := L) (B j), h.p (V.pr g : GS Ω V.S') = 1 := fun j g hg =>
    (hp (resP L Ω g)).trans (ine_NS (hj j).1 (hj j).2.1 ((res_ine _ _).2 hg))
  let π : G (Lp L) Ω →* (globOf r V).Γ := toGS Ω V.S'
  have hπ : Continuous π := continuous_toGS Ω V.S'
  have h2 : ∀ j, ∀ g ∈ GlobalTheory.TameQuot.ineKer L (B j) l,
      ((V.pr g : GS Ω V.S') : (globOf r V).Γ) ∈ PL l (H.comap h.p) := by
    rintro j _ ⟨g, hg, rfl⟩
    refine prokerPL l (globOf r V).Γ (Ine (F := L) (B j))
      (π.comp ((resP L Ω).comp (Ine (F := L) (B j)).subtype)) (H.comap h.p)
      (hπ.comp (continuous_resP.comp continuous_subtype_val)) (fun x => ?_) g hg
    have : h.p (π (resP L Ω x)) = 1 := h1 j x x.2
    show h.p (π (resP L Ω x)) ∈ H
    rw [this]
    exact H.one_mem
  refine ⟨h1, h2, ?_⟩
  haveI := PL_normal l (H.comap h.p)
  set N : Subgroup (globOf r V).Γ := Subgroup.normalClosure (Set.range fun j => ((V.pr (τ j) : GS Ω V.S') : (globOf r V).Γ))
    ⊔ PL l (H.comap h.p) with hN
  haveI : N.Normal := by rw [hN]; infer_instance
  haveI hK : N.topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _
  have hc : IsClosed ((N.topologicalClosure.comap π : Subgroup (G (Lp L) Ω)) : Set (G (Lp L) Ω)) :=
    (Subgroup.isClosed_topologicalClosure N).preimage hπ
  have h3 : ∀ j, ∀ g ∈ Ine (F := L) (B j), π (resP L Ω g) ∈ N.topologicalClosure := fun j g hg => by
    have hc' : IsClosed (((N.topologicalClosure.comap π).comap (resP L Ω) : Subgroup (G L Ω)) : Set (G L Ω)) :=
      hc.preimage continuous_resP
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hc' ((hj j).2.2.2.2 hg)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.le_topologicalClosure N
        ((le_sup_left : _ ≤ N) (Subgroup.subset_normalClosure ⟨j, rfl⟩))
    · intro x hx
      exact Subgroup.le_topologicalClosure N ((le_sup_right : _ ≤ N) (h2 j x hx))
  have h4 : NS Ω V0.S' ≤ N.topologicalClosure.comap π := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨u, hu, A, hA, ht⟩ := ht
    by_cases hu' : u ∈ V.S'
    · rw [hS] at hu'
      obtain ⟨j, rfl⟩ := hu'.resolve_left hu
      obtain ⟨g, hg⟩ := conj_ine (hj j).2.1 hA
      have h5 := hg t ht
      obtain ⟨x, hx⟩ := (hj j).2.2.1 (Ine_le_Dec _ h5)
      have h6 : g⁻¹ * t * g ∈ N.topologicalClosure.comap π := by
        rw [← hx] at h5 ⊢
        exact h3 j x ((res_ine _ _).1 h5)
      have h7 := (hK.comap π).conj_mem _ h6 g
      rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at h7
    · have : π t = 1 := ine_NS hu' hA ht
      show π t ∈ N.topologicalClosure
      rw [this]
      exact one_mem _
  intro x hx
  obtain ⟨g, rfl⟩ : ∃ g, π g = x := QuotientGroup.mk_surjective x
  have h8 : toGS Ω V0.S' g = 1 := (hp g).symm.trans hx
  exact h4 ((QuotientGroup.eq_one_iff g).1 h8)
end

