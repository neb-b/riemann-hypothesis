module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.CtrlMu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaSphRed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphAtTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.PlainOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.QuadBC2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdConjUnl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdExpTor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaCtrlMu
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) (i : ℕ) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h0 : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
    letI : Algebra A (Polynomial B) := ((algebraMap B (Polynomial B)).comp f).toAlgebra
    let φ : Polynomial A →ₐ[A] Polynomial B :=
      { Polynomial.mapRingHom f with commutes' := fun a => Polynomial.map_C f }
    have h := D.nat (Polynomial A) (Polynomial B) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1))
    refine Eq.trans ?_ h
    change D.D (Polynomial B) _ = D.D (Polynomial B) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
    congr 1
    simp [map_sub, MonoidAlgebra.mapRingHom_single]
  simp [W.GDet.lam, h0]
private theorem red_abs {O R T : Type} [CommRing O] [CommRing R] [CommRing T] [Algebra O R] [Algebra O T] (f : R →ₐ[O] T)
    (I : Ideal T) (S : Subalgebra O T) (hS : ∀ s ∈ S, ∀ k : ℕ, s ^ k ∈ I → s ∈ I) (U : Set R)
    (hU : ∀ u ∈ U, ∃ s ∈ S, f u - s ∈ I) (t : R) (ht : t ∈ Algebra.adjoin O U) (k : ℕ) (hk : f (t ^ k) ∈ I) : f t ∈ I := by
  have key : ∃ s ∈ S, f t - s ∈ I := by
    clear hk
    induction ht using Algebra.adjoin_induction with
    | mem x hx => exact hU x hx
    | algebraMap b => exact ⟨_, S.algebraMap_mem b, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨s', hs', h2⟩ := hy
      refine ⟨s + s', add_mem hs hs', ?_⟩
      have := I.add_mem h1 h2
      rw [map_add (f := _)]; convert this using 1; ring
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨s', hs', h2⟩ := hy
      refine ⟨s * s', mul_mem hs hs', ?_⟩
      have := I.add_mem (I.mul_mem_left (f x) h2) (I.mul_mem_left s' h1)
      rw [map_mul]; convert this using 1; ring
  obtain ⟨s, hs, h1⟩ := key
  have e : Ideal.Quotient.mk I (f t) = Ideal.Quotient.mk I s := Ideal.Quotient.eq.2 h1
  have h2 : s ^ k ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← e, ← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hk
  have := I.add_mem h1 (hS s hs k h2)
  simpa using this
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.ctrlMu_of_arith_weight :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ (x : A →ₐ[c.O] c.O) (lam : Wt L l n), lam ∈ H.admitted → H.Arith θ ((Algebra.ofId c.O (Qbar l)).comp x).toRingHom lam →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Module.Finite A (H.MK θ a K)] (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq)
      (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (μ : R →+* Module.End A (H.MK θ a K)),
      (H.MK θ a K = ⊥ ∨ ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K),
        H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))) →
      ∀ t ∈ Algebra.adjoin c.O {b : R | ∃ i g, b = D₀.lam i (MonoidAlgebra.single g 1)}, ∀ k : ℕ,
        (∀ y, μ (t ^ k) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K))) →
        ∀ y, μ t y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K)) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam hl har a K _ R _ _ D₀ ψ₀ μ hμ t ht k hk y
  rcases hμ with h0 | ⟨_, _, f, hf, hμ⟩
  · have : μ t y = 0 := Subtype.ext ((Submodule.mem_bot A).1 (h0 ▸ (μ t y).2))
    rw [this]
    exact zero_mem _
  haveI := c.dvr
  have hker : RingHom.ker ((Algebra.ofId c.O (Qbar l)).comp x) = RingHom.ker x := by
    ext b
    rw [RingHom.mem_ker, RingHom.mem_ker]
    exact map_eq_zero_iff (algebraMap c.O (Qbar l)) Subtype.val_injective
  obtain ⟨I, hI, hfin⟩ := Th.AnnihilatorQuotientFinite.annFin x (heckeAlg (H.MK θ a K) (H.op A)).val.toRingHom fun o y => by
    rw [IsScalarTower.algebraMap_apply c.O A (H.TK θ a K)]
    rfl
  have h1 := red_abs f I (Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)))
    (fun s hs k hk => (hI s).2 (by
      have := _root_.UpperTheory.V.Th.AnnihilatorQuotientFinite.sphRed_alt L Ω l n c H hH A θ hθ ι P hP _ lam hl har a K s hs k
      rw [hker] at this
      exact this ((hI _).1 hk))) _ (by
      rintro _ ⟨i, g, rfl⟩
      refine Th.AnnihilatorQuotientFinite.closedSub I _ _ fun N => ?_
      have := Th.AnnihilatorQuotientFinite.frobS L Ω l n c H hH A θ a K _ _ _ hf i g N
      rwa [lam_map] at this) t ht k ((hI _).2 fun y => by
      have := hk y
      rwa [hμ] at this)
  rw [hμ]
  exact (hI _).1 h1 y
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KatoTwoWOfPublishedH
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords
theorem locQ_of_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (hR : RowT) (hQ : Z.Bc.QuadBC2) : LocQ :=
  locQ plainRec plainOf recTExists (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.base_change_split_of_printed_quad_bc P hQ) potOf
    (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.local_k_of_printed_rec_compat_sph_frob P recTExists (compatTOf hR plainRec) plainRec (winPt Z.Gam.suppFacts Z.ImaginaryQuadraticEtaCharacter.winOf) (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.recSph_alt P) (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.recFrob_alt P))
theorem katoTwoW_of_printsH_of_rT_of_quadBC2 (P : _root_.UpperTheory.V.Af.HypothesesH') (hR : RowT) (hQ : Z.Bc.QuadBC2) : KatoTwoW := by
  intro l _ Ω _ _ _ K _ _ _ e N θ ψ W u ι f hf hW
  have hL := _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.locQ_of_alt P.toClassicalTheorems hR hQ
  obtain ⟨hdt, ha⟩ := u.adm hf
  refine twoS P.toClassicalTheorems.litN.coh (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.srcS_alt P (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.twNew_alt P) (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.frobRoot_alt P.toClassicalTheorems hL)) l Ω K e N θ ψ W u ι f hf ?_
  refine sphOfWit (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.twWit_alt P.toClassicalTheorems (_root_.UpperTheory.V.Z.Win.aIsoTwOf_alt flagLaws Z.ImaginaryQuadraticEtaCharacter.winTw)) hL l u.l_odd Ω ι e u.e_pos W ha.cont
    (GlobalTheory.Ord2.IrrTransfer.isIrr_of_range W (W.comp (GlobalTheory.Ord2.H0g W).subtype) (fun s => ⟨(s : G ℚ Ω), rfl⟩) ha.irr) ?_ hW
  obtain ⟨M, hM, hMk⟩ := UpperTheory.V.CF.kwAbs Ω (GlobalTheory.Ord2.dt W).ker (GlobalTheory.Ord2.TwDet.ker_open ha.cont ha.det2)
    (Abelianization.commutator_subset_ker (GlobalTheory.Ord2.dt W))
  exact ⟨M, hM, fun s hs => hMk s hs⟩
theorem katoTwoW_of_printsH (P : _root_.UpperTheory.V.Af.HypothesesH') : KatoTwoW :=
  _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.katoTwoW_of_printsH_of_rT_of_quadBC2 P (_root_.UpperTheory.Gal.SV.rowOf' P.toClassicalTheorems.litN.aut.gal) UpperTheory.ConvolutionTheory.R2.quadBC2
end UpperTheory.V.Z.Kato.WeilSphericalRecords
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2SmulKey
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem sk_hecke {A M ι ι₀ : Type} [CommRing A] [AddCommGroup M] [Module A M] (Y Y₀ : Submodule A M)
    (op : ι → Module.End A M) (op₀ : ι₀ → Module.End A M) [h : Fact (CommOn Y op)] [h₀ : Fact (CommOn Y₀ op₀)] (j : ι → ι₀)
    (hop : ∀ i, op i = op₀ (j i)) (hm : ∀ f, f ∈ Y ↔ f ∈ Y₀) :
    ∃ φ : heckeAlg Y op →ₐ[A] heckeAlg Y₀ op₀, (∀ i, φ (heckeGen Y op i) = heckeGen Y₀ op₀ (j i)) ∧
      ∀ (t : heckeAlg Y op) (y : Y) (y₀ : Y₀), y.1 = y₀.1 →
        ((t : Module.End A Y) y).1 = ((φ t : Module.End A Y₀) y₀).1 := by
  have hle : Y₀ ≤ Y := fun f hf => (hm f).2 hf
  obtain ⟨φ, h1, h2⟩ := levelUR2HeckeMap A M M ι₀ ι Y₀ Y op₀ op (Submodule.inclusion hle) j
    (Submodule.inclusion_injective hle) fun i y => by
      rw [hop]
      rfl
  refine ⟨φ, h1, fun t y y₀ e => ?_⟩
  have e' : y = Submodule.inclusion hle y₀ := Subtype.ext e
  rw [e', ← h2]
  rfl
private theorem sk_bot {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y Y₀ : Submodule A M}
    (hm : ∀ f, f ∈ Y ↔ f ∈ Y₀) : Y = ⊥ ↔ Y₀ = ⊥ := by
  rw [Submodule.ext hm]
private theorem sk_zero {A M R : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y Y₀ : Submodule A M}
    (hY : Y = ⊥) (ν : R → Y → M) (hν : ∀ t, ν t 0 = 0) (μ : Module.End A Y₀) (t : R) (y : Y) (y₀ : Y₀) (e : y.1 = y₀.1) :
    ν t y = (μ y₀).1 := by
  have h : y = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hY _ y.2)
  have h₀ : y₀ = 0 := Subtype.ext (e.symm.trans (congrArg Subtype.val h))
  rw [h, h₀, hν, map_zero]
  rfl
private theorem sk_comp {O : Type} [CommRing O] {R R₀ T T₀ : Type} [CommRing R] [Algebra O R] [CommRing R₀] [Algebra O R₀]
    [CommRing T] [Algebra O T] [CommRing T₀] [Algebra O T₀] (f : R →ₐ[O] T) (f₀ : R₀ →ₐ[O] T₀) (β : R →ₐ[O] R₀)
    (Φ : T →ₐ[O] T₀) (φ : T →+* T₀) (hφ : ∀ x, Φ x = φ x) {n : ℕ} {G G₀ V : Type} {Γ : V → Type} [Group G] [Group G₀]
    [∀ v, Group (Γ v)] (p : G →* G₀) (D : W.GDet n R G) (ψ : ∀ v, Fin n → Γ v →* Rˣ)
    (D₀ : W.GDet n R₀ G₀) (ψ₀ : ∀ v, Fin n → Γ v →* R₀ˣ)
    (hD : D.map β.toRingHom = D₀.comap p) (hψ : ∀ v i, W.pushCh β.toRingHom (ψ v i) = ψ₀ v i)
    (hu : ∀ f g : R →ₐ[O] T₀, D.map f.toRingHom = D.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g)
    (h : (D.map f.toRingHom).map φ = (D₀.map f₀.toRingHom).comap p ∧
      ∀ v i, W.pushCh φ (W.pushCh f.toRingHom (ψ v i)) = W.pushCh f₀.toRingHom (ψ₀ v i)) (t : R) :
    φ (f t) = f₀ (β t) := by
  obtain rfl : φ = Φ.toRingHom := RingHom.ext fun x => (hφ x).symm
  have e : Φ.comp f = f₀.comp β := by
    refine hu _ _ ?_ fun v i => ?_
    · have e1 : D.map (Φ.comp f).toRingHom = (D.map f.toRingHom).map Φ.toRingHom := ((CA.d_gmap D).2.1 _ _).symm
      have e2 : D.map (f₀.comp β).toRingHom = (D.map β.toRingHom).map f₀.toRingHom := ((CA.d_gmap D).2.1 _ _).symm
      rw [e1, e2, h.1, hD]
      rfl
    · have e := h.2 v i
      rw [← hψ] at e
      exact e
  exact DFunLike.congr_fun e t
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.levelUR2SmulKey_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q₀ τ₀).X.I.T →* Aˣ), (hset Q₀ τ₀).IsWt θ →  ∀ (a : (hset Q₀ τ₀).Op → c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q τ₀).Op → (hset Q₀ τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → ∀ (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O), (hset Q τ₀).IsWt θ' → @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ → (∀ i, a' i = a (j i)) → (∀ i, (hset Q τ₀).op A i = (hset Q₀ τ₀).op A (j i)) → (∀ f : (hset Q₀ τ₀).X.Fn A m, f ∈ (hset Q τ₀).MK θ' a' K ↔ f ∈ (hset Q₀ τ₀).MK θ a K₀) → ∀ (R₀ R : Type) [CommRing R₀] [Algebra c.O R₀] [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R₀ V₀.frame.G₀) (ψ₀ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* R₀ˣ) (D : W.GDet n R V.frame.G₀) (ψ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* Rˣ) (β : R →ₐ[c.O] R₀), D.map β.toRingHom = D₀.comap p → (∀ v i, W.pushCh β.toRingHom (ψ v i) = ψ₀ v i) → (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D.map f.toRingHom = D.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g) → ∀ μ : R₀ →+* Module.End A ((hset Q₀ τ₀).MK θ a K₀), ((hset Q₀ τ₀).MK θ a K₀ = ⊥ ∨ ∃ (_ : Fact (CommOn ((hset Q₀ τ₀).MK θ a K₀) ((hset Q₀ τ₀).op A))) (_ : Alg.IsCO c.O ((hset Q₀ τ₀).TK θ a K₀)) (f : R₀ →ₐ[c.O] (hset Q₀ τ₀).TK θ a K₀), (hset Q₀ τ₀).IsMap θ a K₀ D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A ((hset Q₀ τ₀).MK θ a K₀))) → ∀ ν : R → (hset Q τ₀).MK θ' a' K → (hset Q₀ τ₀).X.Fn A m, (∀ t, ν t 0 = 0) → (∀ [Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A))] [Alg.IsCO c.O ((hset Q τ₀).TK θ' a' K)], ∃ f : R →ₐ[c.O] (hset Q τ₀).TK θ' a' K, (hset Q τ₀).IsMap θ' a' K D ψ f ∧ ∀ t y, ν t y = ((f t : Module.End A ((hset Q τ₀).MK θ' a' K)) y).1) → ∀ t (y : (hset Q τ₀).MK θ' a' K) (y₀ : (hset Q₀ τ₀).MK θ a K₀), y.1 = y₀.1 → ν t y = (μ (β t) y₀).1 := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ A _ _ _ θ hθ a K₀ K p hp hps hpr j hj1 hj2 θ' a' hθ' hθθ ha hop hm
    R₀ R _ _ _ _ D₀ ψ₀ D ψ β hD hψ hu μ hμ ν hν0 hν t y y₀ hy
  by_cases hne : (hset Q τ₀).MK θ' a' K = ⊥
  · exact sk_zero hne ν hν0 (μ (β t)) t y y₀ hy
  have hAx := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c m τ₀
  haveI hF : Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A)) :=
    ⟨((hiComm L Ω l n c _ hAx A θ' hθ' K).2.2.2 a').1⟩
  obtain ⟨hCO, -⟩ := hiAlg L Ω l n c _ hAx A θ' hθ' a' K hne
  obtain ⟨f, hf, hνf⟩ := hν
  obtain ⟨hF₀, hCO₀, f₀, hf₀, hμf⟩ := hμ.resolve_left fun h => hne ((sk_bot hm).2 h)
  obtain ⟨φ, hg, hφ⟩ : ∃ φ : (hset Q τ₀).TK θ' a' K →ₐ[A] (hset Q₀ τ₀).TK θ a K₀,
      (∀ i, φ ((hset Q τ₀).gen θ' a' K i) = (hset Q₀ τ₀).gen θ a K₀ (j i)) ∧
      ∀ (t : (hset Q τ₀).TK θ' a' K) (y : (hset Q τ₀).MK θ' a' K) (y₀ : (hset Q₀ τ₀).MK θ a K₀), y.1 = y₀.1 →
        ((t : Module.End A ((hset Q τ₀).MK θ' a' K)) y).1 = ((φ t : Module.End A ((hset Q₀ τ₀).MK θ a K₀)) y₀).1 :=
    sk_hecke _ _ _ _ (h := hF) (h₀ := hF₀) j hop hm
  have hB := _root_.UpperTheory.V.Hi.levelUR2BaseEq_alt hN l L Ω s n hn V₀ V Q₀ Q c m τ₀ A θ hθ a K₀ K p hp hps hpr j hj1 hj2 θ' a' hθ' hθθ ha
    _ _ hf₀ _ _ hf φ hg
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (hset Q τ₀).TK θ' a' K →ₐ[c.O] (hset Q₀ τ₀).TK θ a K₀, ∀ x, Φ x = φ x :=
    ⟨φ.restrictScalars c.O, fun _ => rfl⟩
  have e := sk_comp f f₀ β Φ φ.toRingHom hΦ p D ψ D₀ ψ₀ hD hψ (hu _) hB t
  refine (hνf t y).trans ((hφ (f t) y y₀ hy).trans ?_)
  exact congrArg (fun u : Module.End A ((hset Q₀ τ₀).MK θ a K₀) => (u y₀).1)
    ((congrArg Subtype.val e).trans (hμf (β t)).symm)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocOkLevelModuleOfThetaData
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem exists_place_above_prime_bis (K : Type) [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  haveI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K) (Ideal.span {(l : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (RingHom.injective_int _)]; exact bot_le)
  have hm : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hl.out.ne_zero (by exact_mod_cast hm)
private theorem trace_map_ring_hom {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (y : MonoidAlgebra A G) : (D.map f).tr (MonoidAlgebra.mapRingHom G f y) = f (D.tr y) :=
  ((UpperTheory.V.CA.d_gmap D).2.2.1 f y).2 1
private theorem trace_map_comp {n : ℕ} {A B C G : Type} [CommRing A] [CommRing B] [CommRing C] [Group G] (D : GDet n A G)
    (f : A →+* B) (g : B →+* C) (k : A →+* C) (hk : g.comp f = k) (y : MonoidAlgebra B G) :
    g ((D.map f).tr y) = (D.map k).tr (MonoidAlgebra.mapRingHom G g y) := by
  rw [← trace_map_ring_hom, (UpperTheory.V.CA.d_gmap D).2.1, hk]
private theorem charpoly_of_representation {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K)
    (y : MonoidAlgebra K G) : (GDet.ofRep ρ).chi y = (GDet.repAlg ρ K y).charpoly := by
  change (GDet.repAlg ρ (Polynomial K) _).det = Matrix.det _
  congr 1
  have h : GDet.repAlg ρ (Polynomial K) (MonoidAlgebra.mapRingHom G Polynomial.C y) =
      (Polynomial.C : K →+* Polynomial K).mapMatrix (GDet.repAlg ρ K y) := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => ext i j; simp [GDet.repAlg]
  rw [map_sub, h, Matrix.charmatrix]
  congr 1
  exact (GDet.repAlg ρ (Polynomial K)).commutes Polynomial.X
private theorem trace_eq_zero_of_rep_eq_zero {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K)
    (y₀ y : MonoidAlgebra K G) (h₀ : (GDet.ofRep ρ).tr y₀ = 0) (h : GDet.repAlg ρ K y = 0) : (GDet.ofRep ρ).tr y = 0 := by
  rcases n with _ | n
  · rw [← h₀, GDet.tr, GDet.tr, GDet.lam, GDet.lam, charpoly_of_representation, charpoly_of_representation, Subsingleton.elim (GDet.repAlg ρ K y) (GDet.repAlg ρ K y₀)]
  · nontriviality K
    rw [GDet.tr, GDet.lam, charpoly_of_representation, h, Matrix.charpoly_zero, Polynomial.coeff_X_pow]
    simp
private theorem map_ring_hom_first_relation {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (g ph : G) (u : Fin n → A) :
    MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g 1 * q1El ph u) = MonoidAlgebra.single g 1 * q1El ph fun i => f (u i) := by
  simp only [q1El, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, MonoidAlgebra.mapRingHom_single, map_one]
private theorem map_ring_hom_second_relation {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (g ph ta : G) (u : Fin n → A)
    (i : Fin n) (y : A) : MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g 1 * q2El ph ta u i y) =
      MonoidAlgebra.single g 1 * q2El ph ta (fun i => f (u i)) i (f y) := by
  simp only [q2El, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, apply_ite (MonoidAlgebra.mapRingHom G f),
    MonoidAlgebra.mapRingHom_single, map_one]
private theorem rep_single_eq_smul {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K) (g : G) (a : K) :
    GDet.repAlg ρ K (MonoidAlgebra.single g a) = a • ρ g := by
  ext i j; simp [GDet.repAlg]
private theorem rep_first_relation_eq_zero {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K) (g ph : G)
    (α : Fin n → K) (h : (ρ ph).charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) :
    GDet.repAlg ρ K (MonoidAlgebra.single g 1 * q1El ph α) = 0 := by
  have h1 := Matrix.aeval_self_charpoly (ρ ph)
  rw [h, ← List.prod_ofFn, map_list_prod, List.map_ofFn] at h1
  rw [map_mul, q1El, map_list_prod, List.map_ofFn]
  refine mul_eq_zero_of_right _ (Eq.trans ?_ h1)
  congr 2
  funext i
  simp [rep_single_eq_smul, Algebra.algebraMap_eq_smul_one]
private theorem rep_second_relation_eq_zero {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K) (g ph ta : G)
    (α : Fin n → K) (i : Fin n) (c : K)
    (h : (List.ofFn fun i' => if i' = i then 1 else ρ ph - α i' • (1 : Matrix (Fin n) (Fin n) K)).prod *
      (ρ ta - c • (1 : Matrix (Fin n) (Fin n) K)) = 0) :
    GDet.repAlg ρ K (MonoidAlgebra.single g 1 * q2El ph ta α i (c - 1)) = 0 := by
  rw [map_mul, q2El, map_mul, map_list_prod, List.map_ofFn]
  refine mul_eq_zero_of_right _ (Eq.trans ?_ h)
  congr 1
  · congr 2
    funext k
    by_cases hk : k = i <;> simp [hk, rep_single_eq_smul]
  · simp [rep_single_eq_smul, sub_smul]
private theorem reduction_of_polynomial_element {n q : ℕ} {R G E : Type} [CommRing R] [Group G] [Ring E] [Algebra R E] (D : GDet n R G)
    (act : PUY R q n →ₐ[R] E) (Nq : Fin q → ℕ) (j : Fin q) (k : ℕ) (z : MonoidAlgebra (MvPolynomial (Fin n ⊕ Fin n) R) G)
    (z' : MonoidAlgebra (PUY R q n) G)
    (hz : MonoidAlgebra.mapRingHom G (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i)) :
      MvPolynomial (Fin n ⊕ Fin n) R →ₐ[R] PUY R q n).toRingHom z = z')
    (h : act (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i))
      ((∏ i : Fin n, ∏ i' ∈ Finset.univ.erase i, ((MvPolynomial.X (.inl i) - MvPolynomial.X (.inl i')) *
        (MvPolynomial.X (.inl i) - (Nq j : MvPolynomial (Fin n ⊕ Fin n) R) * MvPolynomial.X (.inl i')))) *
        (D.map (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)).tr z) ^ k) = 0) :
    act ((fEl Nq (uV R) * (D.map (MvPolynomial.C : R →+* PUY R q n)).tr z') ^ k) = 0 := by
  have e := trace_map_comp D (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)
    (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i)) :
      MvPolynomial (Fin n ⊕ Fin n) R →ₐ[R] PUY R q n).toRingHom MvPolynomial.C (by ext : 1; simp) z
  rw [hz] at e
  rw [fEl, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_assoc, mul_pow, map_mul, ← e]
  refine mul_eq_zero_of_right _ (Eq.trans ?_ h)
  simp [map_prod]
private theorem trace_vanishing_of_evaluation {n : ℕ} {R K G : Type} [CommRing R] [CommRing K] [Group G] (D : GDet n R G) (θ : R →+* K) (ι : K →+* ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) K) (hD : D.map θ = GDet.ofRep ρ) (z₀ : MonoidAlgebra R G) (h₀ : D.tr z₀ = 0)
    (v : Fin n ⊕ Fin n → ℂ) (z : MonoidAlgebra (MvPolynomial (Fin n ⊕ Fin n) R) G)
    (h : GDet.repAlg (ι.mapMatrix.toMonoidHom.comp ρ) ℂ
      (MonoidAlgebra.mapRingHom G (MvPolynomial.eval₂Hom (ι.comp θ) v) z) = 0) :
    MvPolynomial.eval₂ (ι.comp θ) v ((D.map (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)).tr z) = 0 := by
  have hD' : D.map (ι.comp θ) = GDet.ofRep (ι.mapMatrix.toMonoidHom.comp ρ) := by
    rw [← (UpperTheory.V.CA.d_gmap D).2.1, hD, (UpperTheory.V.CA.d_gmap (GDet.ofRep ρ)).2.2.2]
  rw [← MvPolynomial.coe_eval₂Hom, trace_map_comp D _ _ (ι.comp θ) (by ext : 1; simp), hD']
  refine trace_eq_zero_of_rep_eq_zero _ (MonoidAlgebra.mapRingHom G (ι.comp θ) z₀) _ ?_ h
  rw [← hD', trace_map_ring_hom, h₀, map_zero]
theorem UpperTheory.V.Z.Win.T2.level_relation_one_two :
    _root_.UpperTheory.V.Pa.Lev.LevelRelationOneTwo := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ h1 h2 h3 T ph ta ⟨ι, hsep, hloc⟩
  obtain ⟨v⟩ : Nonempty (globOf r V).frame.Vl := (exists_place_above_prime_bis (Lp L) l).elim fun v hv => ⟨⟨v, hv⟩⟩
  have h₀ := A.p.Ord v (fun _ => 1) 1
  refine ⟨fun j g => ?_, fun j i g => ?_⟩
  · refine reduction_of_polynomial_element A.p.D T.act1 (qj w) j _ (MonoidAlgebra.single g 1 * q1El (ph j) fun i => MvPolynomial.X (.inl i)) _
      ((map_ring_hom_first_relation _ _ _ _).trans (by simp)) ?_
    refine _root_.UpperTheory.V.Pa.Lev.relOf_alt hP l L Ω s V0 O n r B J D b V h q w A x δ h1 h2 h3 T ι hsep j _ fun y θ hθ χ hχ => ?_
    rw [MvPolynomial.eval₂_mul]
    refine mul_eq_zero.2 (or_iff_not_imp_left.2 fun hne => ?_)
    refine trace_vanishing_of_evaluation A.p.D y.θ ι.toRingHom (mat y.rep) y.det _ h₀ _ _ ?_
    rw [map_ring_hom_first_relation]
    refine rep_first_relation_eq_zero _ _ _ _ ?_
    simp only [MvPolynomial.eval₂Hom_X', Sum.elim_inl]
    refine (_root_.UpperTheory.V.Z.Win.relT' (hloc y j) _ le_rfl θ hθ χ hχ _ fun _ => rfl).1 (Or.inr fun a a' ha => ?_)
    rw [← MvPolynomial.coe_eval₂Hom] at hne
    simp only [map_prod, map_mul, map_sub, map_natCast, MvPolynomial.eval₂Hom_X', Sum.elim_inl] at hne
    have h4 := Finset.prod_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 hne a (Finset.mem_univ _)) a'
      (Finset.mem_erase.2 ⟨ha.symm, Finset.mem_univ _⟩)
    exact ⟨sub_ne_zero.1 (left_ne_zero_of_mul h4), sub_ne_zero.1 (right_ne_zero_of_mul h4)⟩
  · refine reduction_of_polynomial_element A.p.D T.act1 (qj w) j _
      (MonoidAlgebra.single g 1 * q2El (ph j) (ta j) (fun i => MvPolynomial.X (.inl i)) i (MvPolynomial.X (.inr i))) _
      ((map_ring_hom_second_relation _ _ _ _ _ _ _).trans (by simp)) ?_
    refine _root_.UpperTheory.V.Pa.Lev.relOf_alt hP l L Ω s V0 O n r B J D b V h q w A x δ h1 h2 h3 T ι hsep j _ fun y θ hθ χ hχ => ?_
    rw [MvPolynomial.eval₂_mul]
    refine mul_eq_zero.2 (or_iff_not_imp_left.2 fun hne => ?_)
    refine trace_vanishing_of_evaluation A.p.D y.θ ι.toRingHom (mat y.rep) y.det _ h₀ _ _ ?_
    rw [map_ring_hom_second_relation]
    simp only [MvPolynomial.eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]
    refine rep_second_relation_eq_zero _ _ _ _ _ _ _ ((_root_.UpperTheory.V.Z.Win.relT' (hloc y j) _ le_rfl θ hθ χ hχ _ fun _ => rfl).2 (fun a a' ha => ?_) i)
    rw [← MvPolynomial.coe_eval₂Hom] at hne
    simp only [map_prod, map_mul, map_sub, map_natCast, MvPolynomial.eval₂Hom_X', Sum.elim_inl] at hne
    have h4 := Finset.prod_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 hne a (Finset.mem_univ _)) a'
      (Finset.mem_erase.2 ⟨ha.symm, Finset.mem_univ _⟩)
    exact ⟨sub_ne_zero.1 (left_ne_zero_of_mul h4), sub_ne_zero.1 (right_ne_zero_of_mul h4)⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdBornJ
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
private theorem sat_of_frob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l n : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {ρ : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂˣ}
    (h : Af.FrobEig ι ρ w (Af.algSat n (normV w) B)) (h' : Af.FrobEig ι ρ w (Af.algSat n (normV w) B')) : B = B' := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have e := congrArg Polynomial.roots (((h A hA).2 σ hσ).symm.trans ((h' A hA).2 σ hσ))
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e
  have hq : (0 : ℝ) < (normV w : ℕ) := Nat.cast_pos.2 (lt_trans one_pos (one_lt_normV w))
  have hc : (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'
  have e' := Multiset.map_injective (mul_right_injective₀ hc) (a₁ := B.map Units.val) (a₂ := B'.map Units.val)
    (by simpa [Af.algSat, Multiset.map_map] using e)
  exact Multiset.map_injective Units.val_injective e'
theorem UpperTheory.V.Z.Ord.born_j_of_printed_polarization_window :
    _root_.UpperTheory.V.Af.Hypotheses' → ImaginaryQuadraticEtaCharacter.WinOf → BornJ := by
  intro P hO l _ L Ω _ _ _ _ _ _ s n hn V c r ι B Λ J hR hE x h ρ hJ hA hρ hI hc w hl hU
  obtain ⟨π₀, -, hd, ha, he⟩ := hE x h ρ hJ hA hρ hI
  have hl' := (UpperTheory.V.Hi.Pu.l_iff (l := l) w).2 hl
  let v : Vl l L := ⟨w.under (𝓞 (Lp L)), hl'⟩
  have hu : (s.w v.1).under (𝓞 (Lp L)) = v.1 := UpperTheory.V.Hi.Pu.w_under s v.1
  have hsl : ((l : ℕ) : 𝓞 L) ∈ (s.w v.1).asIdeal := (UpperTheory.V.Hi.Pu.l_iff (l := l) _).1 (by rw [hu]; exact hl')
  have hF := _root_.UpperTheory.V.Z.Ord.flagJ_alt P.litN l L Ω s n V c r B Λ J hR x h ρ hJ hA hρ hI v
  obtain ⟨hu1, hu2⟩ := _root_.UpperTheory.V.Z.Ord.conj_unlinked_of_printed_results P L Ω l ι n ρ π₀ hc hd ha (s.w v.1) w hu.symm (s.A v.1) (s.hw v.1) (x.psi v) hF
  obtain ⟨-, hTU, hW⟩ := _root_.UpperTheory.V.Z.Ord.exp_torsion_of_literal_automorphy_n P.litN L Ω l n hn ι (s.A v.1) (s.w v.1) (s.hw v.1) hsl π₀ (x.psi v) (he v)
  have hT : TU π₀ (s.w v.1) := hTU (hu1 hU)
  obtain ⟨t, ht⟩ := hO L n hn π₀
  refine ⟨hu2 (hW t (ht (s.w v.1) hT.1 hT.2)), fun π hπ => ?_⟩
  have e : π₀ = π := GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC L n π₀ π (by
    filter_upwards [ha.2, hπ.2] with u ⟨b, hb, hf⟩ ⟨b', hb', hf'⟩
    obtain rfl := sat_of_frob hf hf'
    exact ⟨b, (CG.hasSat_mk π₀ u b).1 hb, (CG.hasSat_mk π u b).1 hb'⟩))
  exact e ▸ _root_.UpperTheory.V.Z.Ord.conj_torsion_of_printed_results P L n hn π₀ hd (s.w v.1) w hu.symm hT
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVQuadBC
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
theorem UpperTheory.Gal.SV.quad_base_change_w_of_printed_results (_P : _root_.UpperTheory.V.Af.Hypotheses') : UpperTheory.V.Br.QuadBCw := by
  intro F E _ _ _ _ _ _ _ h2 a ha2 _ π hr
  obtain rfl := ha2.out
  exact (UpperTheory.ConvolutionTheory.R2.quadBC2 F E h2 π hr).imp_right fun ⟨P, hP⟩ => ⟨P, UpperTheory.V.Br.IsBCw.of_isBC hP⟩
end
end

