module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdelEqZeroOfOffDom

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameAtSmallPlace
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.TameStab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Groups

variable {G Γ : Type} [Group G] [Group Γ]

def conjIn (H J : Subgroup G) (g : G) : Subgroup G where
  carrier := {x | x ∈ H ∧ g⁻¹ * x * g ∈ J}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    have := J.mul_mem ha' hb'
    convert this using 1
    group
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, ?_⟩
    have := J.inv_mem ha'
    convert this using 1
    group

def conjInEquiv (H J : Subgroup G) (g : G) : {γ : H // g⁻¹ * (γ : G) * g ∈ J} ≃ conjIn H J g where
  toFun γ := ⟨γ.1.1, γ.1.2, γ.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_conj (ι : Γ →* G) (J : Subgroup G) {I : Type} (y : I → G) (hrep : Bridge.IsReps ι J y)
    (hfin : ∀ i, Finite (Bridge.stab ι J (y i))) (g : G) : Finite {γ : ι.range // g⁻¹ * (γ : G) * g ∈ J} := by
  obtain ⟨c, ⟨γ₀, k, hg⟩, -⟩ := hrep g
  haveI := hfin c
  let f : Bridge.stab ι J (y c) → {γ : ι.range // g⁻¹ * (γ : G) * g ∈ J} := fun s =>
    ⟨⟨ι (γ₀ * s * γ₀⁻¹), γ₀ * s * γ₀⁻¹, rfl⟩, by
      have hs : (y c)⁻¹ * ι s * (y c) ∈ J := by
        have := s.2
        simpa [Bridge.stab, Subgroup.mem_comap, MulAut.conj_apply] using this
      have := J.mul_mem (J.mul_mem (J.inv_mem k.2) hs) k.2
      convert this using 1
      rw [hg]
      simp only [map_mul, map_inv]
      group⟩
  refine Finite.of_surjective f ?_
  rintro ⟨⟨_, a, rfl⟩, ha⟩
  refine ⟨⟨γ₀⁻¹ * a * γ₀, ?_⟩, ?_⟩
  · have := J.mul_mem (J.mul_mem k.2 ha) (J.inv_mem k.2)
    simp only [Bridge.stab, Subgroup.mem_comap, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv]
    convert this using 1
    rw [hg]
    simp only [map_mul, map_inv]
    group
  · apply Subtype.ext
    apply Subtype.ext
    show ι (γ₀ * (γ₀⁻¹ * a * γ₀) * γ₀⁻¹) = ι a
    congr 1
    group

end Groups


set_option maxHeartbeats 1600000 in
theorem rat_eq_one {D : D7} (V : TH.HSp D) (l : ℕ) (hl : l.Prime) (hN : V.rank + 1 < l)
    (hirr : Irreducible (Polynomial.cyclotomic l D.host.E)) (x : Bridge.Gf V) (hx : x ∈ (Bridge.ratF V).range)
    (hxl : x ^ l = 1) : x = 1 := by
  obtain ⟨q, rfl⟩ := hx
  have hq := q.2
  simp only [Formalism.L2.Theta.GQ, GlobalTheoryTheory.GenusMassVolumes.HFinIn, Subgroup.mem_subgroupOf, GlobalTheoryTheory.GenusMassVolumes.HFin, Subgroup.mem_map] at hq
  obtain ⟨u, -, hu⟩ := hq
  let φ : D.host.E →+* GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom.comp
      (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F))
  have key : ((Bridge.ratF V q : Bridge.Gf V) : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val = u.val.map φ := by
    have hu' : (q.1 : Formalism.L2.Theta.GA D V).1 =
        Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) u := hu.symm
    have h1 : ((Bridge.ratF V q : Bridge.Gf V) : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
        Formalism.UG.bc (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
          (q.1 : Formalism.L2.Theta.GA D V).1 := rfl
    rw [h1, hu']
    ext i j
    rfl
  rcases subsingleton_or_nontrivial (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) with hs | hs
  · apply Subtype.ext
    apply Units.ext
    ext i j
    exact Subsingleton.elim _ _
  · have hφ : Function.Injective φ := φ.injective
    have h2 := congrArg (fun z : Bridge.Gf V => (z : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val) hxl
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one] at h2
    rw [key] at h2
    have h3 : φ.mapMatrix (u.val ^ l) = φ.mapMatrix 1 := by
      rw [map_pow, map_one, RingHom.mapMatrix_apply]
      exact h2
    have hu1 : u.val ^ l = 1 := Matrix.map_injective hφ h3
    have hu2 : u.val = 1 :=
      GlobalTheory.no_order_l_of_cyclotomic_irreducible D.host.E l V.rank _ hl hirr hN hu1
    apply Subtype.ext
    apply Units.ext
    rw [key, hu2]
    have h4 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map φ = 1 := Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)
    rw [h4]
    rfl

theorem tameAt_of_smallAt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m)
    (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hNr : P.Nr = (Vc D j).rank) (hS : SmallAt p j P w) :
    TameAt p j w := by
  obtain ⟨hl, hN, hd, -, -⟩ := hS
  intro g
  have hfin : Finite {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)} :=
    finite_conj (Bridge.ratF (Vc D j)) (levJ p j (p.R.mu w)) (p.R.B.L j (p.R.mu w)).pres.y (p.R.B.L j (p.R.mu w)).pres.reps
      (fun c => Finite.of_equiv _ ((p.R.B.L j (p.R.mu w)).pres.stabI c).toEquiv) g
  refine ⟨hfin, ?_⟩
  intro hdvd
  haveI : Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime := ⟨hl⟩
  rw [Nat.card_congr (conjInEquiv _ _ g)] at hdvd
  haveI : Finite (conjIn (Bridge.ratF (Vc D j)).range (levJ p j (p.R.mu w)) g) := Finite.of_equiv _ (conjInEquiv _ _ g)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (Formalism.EigenvalueLevelCeiling.plc w) hdvd
  have hirr := GlobalTheory.cyclotomic_irreducible_of_not_dvd_discr D.host.E (Formalism.EigenvalueLevelCeiling.plc w) hl hd
  have hxl : (x : Bridge.Gf (Vc D j)) ^ (Formalism.EigenvalueLevelCeiling.plc w) = 1 := by
    rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one]
    rfl
  have h1 := rat_eq_one (Vc D j) (Formalism.EigenvalueLevelCeiling.plc w) hl (hNr ▸ hN) hirr x x.2.1 hxl
  have hx1 : x = 1 := Subtype.ext h1
  rw [hx1, orderOf_one] at hx
  exact hl.one_lt.ne hx

end GlobalTheory.TameStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainTransporterMemDomain
section
set_option autoImplicit false

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

namespace GlobalTheory.TwoLevelsDom

theorem lact_tr_mem_dom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {rr : ℕ} {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E rr U C) (g : U) (c : C) (x : Frame M.Ψ rr), x ∈ M.dom → lact (M.tr g c) x ∈ M.dom :=
  fun M g c _x hx => GlobalTheory.CuspEmb.lact_tr_mem M g c hx

end GlobalTheory.TwoLevelsDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentModIdealOfTrivialModHalfStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_mod_ideal_of_trivial_mod_half : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (L' : Submodule (𝓞 E) (Fin r → E)) (Mb P : Ideal (𝓞 E)), Mb ≤ P →
    ∀ {A : Type} [AddCommGroup A] [Module (𝓞 E) A] (φ : A ≃ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))
      (ℓ : A ≃ₗ[𝓞 E] A) (n : ℤ),
    (∀ x : A, ((ℓ.toLinearMap - LinearMap.id : Module.End (𝓞 E) A) ^ r) x ∈ P • (⊤ : Submodule (𝓞 E) A)) →
    ∀ γ t : Matrix (Fin r) (Fin r) E, (∀ w ∈ L', Matrix.mulVec γ w ∈ L') → (∀ w ∈ L', Matrix.mulVec γ w - w ∈ Mb • L') →
    (∀ w : L', ∃ hw : Matrix.mulVec t w ∈ L',
      Submodule.Quotient.mk (p := Mb • (⊤ : Submodule (𝓞 E) L')) ⟨_, hw⟩ = φ ((ℓ ^ n) (φ.symm (Submodule.Quotient.mk w)))) →
    ∀ w ∈ L', Matrix.mulVec ((γ * t - 1) ^ r) w ∈ P • L' := by
  first | exact @GlobalTheory.UnipModHalf.unip_mod_half | exact GlobalTheory.UnipModHalf.unip_mod_half | (intros; apply GlobalTheory.UnipModHalf.unip_mod_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharIndicatorEqOneOfCongruentOneStatement
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitDetCharIndicator_eq_one_of_congruent_one : ∀ {D : D7} (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 → ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 →
  ∀ {k : ℕ} (P : Matrix (Fin k) (Fin k) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, (P - 1) i j ∈ hatId D 𝔪) →
  unitChar ν e (P.map (toE D)) = 1 := by
  first | exact @GlobalTheory.StdRead.CongOneChar.unitChar_cong | exact GlobalTheory.StdRead.CongOneChar.unitChar_cong | (intros; apply GlobalTheory.StdRead.CongOneChar.unitChar_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunCuspFormReadingLinearIndependent
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ShareOn.Reading
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem castFrame_castFrame_symm {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (hΨ : Ψ = Ψ')
    (x : Frame Ψ' r) : castFrame hΨ (castFrame hΨ.symm x) = x := by
  subst hΨ; rfl


set_option synthInstance.maxHeartbeats 400000 in
theorem rdLin_linearIndependent {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
    {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type}
    [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}
    (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (n : ℕ)
    (b : Fin n → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) :
    LinearIndependent (recB (h.laws v).p.toLawsCore).KO b → LinearIndependent ℂ (fun k => rdLin h ha (b k)) := by
  intro hb
  have hJ := (GlobalTheory.ReadingTieCheck.tieRead_holds (h.laws v).p ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩).2 (p.κ i)
  let b' : Fin n → cusp ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c ((r.used v).full.U ((i : ℕ) + 1))
      (wtA (p.κ i)) (p.κ i).n :=
    fun k => ⟨(b k).1, cutR_le (r.used v).full.C ((i : ℕ) + 1) (p.κ i) (b k).2⟩
  have hb' : LinearIndependent (r.used v).full.Q.c.F b' := by
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    apply Subtype.ext
    have h1 := congrArg Subtype.val hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] at h1 ⊢
    exact h1
  have hR := hJ n b' hb'
  rw [Fintype.linearIndependent_iff] at hR ⊢
  intro g hg
  apply hR g
  have hoff : ∀ k, rdC ((r.used v).full.U ((i : ℕ) + 1)) (r.used v).full.σ₀ (wtA (p.κ i)) (p.κ i).n (b' k) ∈
      offZero ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X :=
    fun k => rdU_mem_offZero _ _
  have claim : ∀ c, (∑ k, g k • rdC ((r.used v).full.U ((i : ℕ) + 1)) (r.used v).full.σ₀ (wtA (p.κ i)) (p.κ i).n
      (b' k)) (e c) = 0 := by
    intro c
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : x ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).dom
    · have hy : castFrame (psi_eq ha c).symm x ∈ M.dom :=
        (mem_dom_iff ha c _).1 (by rw [castFrame_castFrame_symm]; exact hx)
      have := congrFun (congrFun hg c) ⟨_, hy⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, rdLin_apply, rdFun,
        castFrame_castFrame_symm] at this
      exact this
    · exact Finset.sum_eq_zero fun k _ => by rw [hoff k (e c) x hx, mul_zero]
  funext k'
  have := claim (e.symm k')
  rw [e.apply_symm_apply] at this
  exact this

end GlobalTheory.ShareOn.Reading
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunCuspFormReadingMemModelCuspForms
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ShareOn.Reading

theorem cast_mem_SS_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X Y : Data E r} (hXY : X = Y)
    (hΨ : X.Ψ = Y.Ψ) {la : Wt Y.Ψ r} {la' : Wt X.Ψ r}
    (hla : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ Y.Ψ) a, la' ⟨τ, h1⟩ a = la ⟨τ, h2⟩ a) {G : Frame Y.Ψ r → ℂ}
    (hG : G ∈ Y.SS la) : (fun x => G (castFrame hΨ x)) ∈ X.SS la' := by
  subst hXY
  have e : la' = la := by funext τ a; exact hla τ.1 τ.2 τ.2 a
  subst e
  exact hG

theorem rdFun_mem_SS : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), rdFun (v := v) (e := e) h ha F ∈ M.SS ka := by
  intro D L hT Gi Gl Kc Y cX ex Csz p r h i C _ M ka v e ha hb F c
  have key := GlobalTheory.ReadingTieCheck.reading_mem_SS (h.laws v).p ((i : ℕ) + 1) (p.κ i) F (e c)
  exact cast_mem_SS_of_eq (ha c) ((M.comp_Ψ c).trans (psi_eq ha c)) (fun τ h1 h2 a => hb c τ _ h2 a) key

end GlobalTheory.ShareOn.Reading
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunUniformisationCharacterTrivialArithmeticG
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem uAt_chi_eq_one : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp) (la : Wt ((uAt r v i).X k).Ψ D.R.r), ∀ γ ∈ ((uAt r v i).X k).Γ, ((uAt r v i).X k).χ la γ = 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v k la γ hγ
  exact GlobalTheory.OneEmbeddingProbe.chi_eq_one (uAt r v i)
    (fun a n hd k γ hγ => (h.laws v).p.chiTriv ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ _
      (r.used v).full.toCore.good_σ₀ a n hd k γ hγ) k la γ hγ

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunUniformisationComponentsShareCmData
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem comps_share : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ k k' : (uAt r v i).Comp, ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ ∧ ((uAt r v i).X k).p0 = ((uAt r v i).X k').p0 ∧ ((uAt r v i).X k).Gm = ((uAt r v i).X k').Gm ∧ ((uAt r v i).X k).ξ0 = ((uAt r v i).X k').ξ0 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v k k'
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hL := (h.laws v).j
  have hg := (r.used v).full.toCore.good_σ₀
  have hU := hL.unf _ hj _ hg
  obtain ⟨hr, hm⟩ := hL.modelW _ hj _ hg
  refine ⟨?_, ((hU.2.1 k).1.trans (hU.2.1 k').1.symm), ((hm k).1.trans (hm k').1.symm),
    ((hm k).2.trans (hm k').2.symm)⟩
  ext τ
  exact ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm

end GlobalTheory.ShareOn
end

