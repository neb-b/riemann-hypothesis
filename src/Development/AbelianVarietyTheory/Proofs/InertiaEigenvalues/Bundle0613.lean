module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0608
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSublevelFiniteIndexMorePlaces
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SublevelFinIndex

variable {E : Type} [Field E] [NumberField E]

variable {F : Type} [Field F] [NumberField F] [StarRing E] [Algebra F E] {n : ℕ} {LL : Type} [CommRing LL]

theorem parLev_anti (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] GlobalTheoryTheory.GenusMassVolumes.Af F)) (D : LevDat E LL n)
    (Q' : Finset (Pl E)) (xq : ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) (h : D.Q ⊆ Q') :
    parLev hc J β { D with Q := Q', xq := xq } ≤ parLev hc J β D := by
  intro x hx
  have h2 : x ∈ ⨅ PP ∈ Q', parah β PP (blk2 D.r) := hx.2
  have h3 : x ∈ ⨅ PP ∈ D.Q, parah β PP (blk2 D.r) :=
    Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 PP) (h hP)
  exact ⟨hx.1, h3⟩

theorem lev_of_red (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] GlobalTheoryTheory.GenusMassVolumes.Af F)) (D : LevDat E LL n)
    (Q' : Finset (Pl E)) (xq : ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) {x : GL (Fin n) (E ⊗[F] GlobalTheoryTheory.GenusMassVolumes.Af F)}
    (hx : x ∈ lev hc J β D) (hr : ∀ PP ∈ Q', redFn β PP x = 1) : x ∈ lev hc J β { D with Q := Q', xq := xq } := by
  refine ⟨⟨hx.1.1, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_parah.2 ⟨parLev_St hx.1, ?_⟩⟩, hx.2⟩
  rw [hr PP hP]
  exact Subgroup.one_mem _

end GlobalTheory.SublevelFinIndex


open GlobalTheory.SublevelFinIndex in
theorem GlobalTheory.sublevel_finiteIndex : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (levEnv V β { L with Q := Q', xq := xq }).J ≤ (levEnv V β L).J ∧ (levEnv V β { L with Q := Q', xq := xq }).Q ≤ (levEnv V β L).Q ∧ (((levEnv V β { L with Q := Q', xq := xq }).J).subgroupOf (levEnv V β L).J).FiniteIndex ∧ ∀ g : Bridge.Gf V, g ∈ (levEnv V β { L with Q := Q', xq := xq }).Q → g ∈ (levEnv V β L).J → g ∈ (levEnv V β { L with Q := Q', xq := xq }).J := by
  intro D V β Λ _ L Q' xq hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    have h : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L { L with Q := Q', xq := xq }) := hg
    exact (⟨parLev_anti D.sp.cm V.gram β (Lev.flag1L L) Q' xq hQ h.1, h.2⟩ :
      Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L))
  · intro g hg
    have h : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flagL { L with Q := Q', xq := xq }) := hg
    exact (⟨parLev_anti D.sp.cm V.gram β (Lev.flagL L) Q' xq hQ h.1, h.2⟩ :
      Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flagL L))
  · refine ⟨Formalism.UG.P.levelv_relIndex_ne_zero _ _
      (fun (g : Bridge.Gf V) (PP : ↥Q') => redFn β PP.1 (Formalism.UG.bc (Lev.swapAE D) g.1)) ?_⟩
    intro a ha b hb hab
    have hab' : Formalism.UG.bc (Lev.swapAE D) (a⁻¹ * b).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) :=
      (levEnv V β L).J.mul_mem ((levEnv V β L).J.inv_mem ha) hb
    have ha' : Formalism.UG.bc (Lev.swapAE D) a.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) := ha
    have hb' : Formalism.UG.bc (Lev.swapAE D) b.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) := hb
    show Formalism.UG.bc (Lev.swapAE D) (a⁻¹ * b).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L { L with Q := Q', xq := xq })
    refine lev_of_red D.sp.cm V.gram β (Lev.flag1L L) Q' xq hab' fun PP hP => ?_
    have e := congrFun hab ⟨PP, hP⟩
    have hSa := parLev_St ha'.1
    have hSb := parLev_St hb'.1
    simp only at e
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, redFn_mul ((St β).inv_mem hSa) hSb, redFn_inv hSa, e,
      inv_mul_cancel]
  · intro g hgQ hgJ
    have h1 : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flagL { L with Q := Q', xq := xq }) := hgQ
    have h2 : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) := hgJ
    exact (⟨h1.1, h2.2⟩ :
      Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L { L with Q := Q', xq := xq }))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialRankinSelbergProductConjSwapReal
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

noncomputable section

namespace GlobalTheory.RSConj

theorem conj_tprod {β : Type} (f : β → ℂ) :
    starRingEnd ℂ (∏' i, f i) = ∏' i, starRingEnd ℂ (f i) := by
  by_cases hf : Multipliable f
  · exact hf.map_tprod (starRingEnd ℂ) Complex.continuous_conj
  · have hg : ¬ Multipliable fun i => starRingEnd ℂ (f i) := by
      intro hg
      apply hf
      have := hg.map (starRingEnd ℂ) Complex.continuous_conj
      convert this using 1
      funext i
      simp
    rw [tprod_eq_one_of_not_multipliable hf, tprod_eq_one_of_not_multipliable hg, map_one]

theorem conj_natCast_cpow_neg (q : ℕ) (x : ℝ) :
    starRingEnd ℂ ((q : ℂ) ^ (-(x : ℂ))) = (q : ℂ) ^ (-(x : ℂ)) := by
  have h : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
    push_cast
    rfl
  rw [h, Complex.conj_ofReal]

theorem conj_locL (q : ℕ) (A B : Multiset ℂˣ) (x : ℝ) :
    starRingEnd ℂ (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) =
      locL q B (A.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  unfold locL
  rw [map_multiset_prod]
  simp only [SProd.sprod, Multiset.product, Multiset.map_bind, Multiset.prod_bind, Multiset.map_map, Function.comp_def]
  rw [Multiset.prod_map_prod_map]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp only [map_inv₀, map_sub, map_one, map_mul, conj_natCast_cpow_neg, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Complex.conj_conj]
  ring

theorem partial_conj : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b),
    σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' →
    ∀ x : ℝ, 1 < x → ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1 =
      starRingEnd ℂ (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) := by
  intro E _ _ _ a b σ σ' _ _ T _ _ x _
  rw [conj_tprod]
  congr 1
  funext w
  exact (conj_locL _ _ _ x).symm

end GlobalTheory.RSConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAdelicRationalPointsComm
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section General

variable {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]

variable [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
  [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]

def swapEquiv (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂] :
    (G₂ × G₁) ≃ₜ+ (G₁ × G₂) :=
  { AddEquiv.prodComm with
    continuous_toFun := continuous_swap
    continuous_invFun := continuous_swap }

theorem avg_comm_of_isCoLat {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂)
    (Φ : G₁ × G₂ → ℂ) (hΦ : Per (Γ₁.prod Γ₂) Φ) :
    avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) = avg Γ₂ (fun y => avg Γ₁ (fun x => Φ (x, y))) := by
  have hs : Per (Γ₂.prod Γ₁) (fun p : G₂ × G₁ => Φ (p.2, p.1)) := by
    refine ⟨hΦ.1.comp continuous_swap, fun γ hγ x => ?_⟩
    exact hΦ.2 (γ.2, γ.1) ⟨hγ.2, hγ.1⟩ (x.2, x.1)
  have a := GlobalTheory.T.quotientAverage_prod_fubini G₁ G₂ Γ₁ Γ₂ h₁ h₂ Φ hΦ
  have b := GlobalTheory.T.quotientAverage_prod_fubini G₂ G₁ Γ₂ Γ₁ h₂ h₁ _ hs
  have c := _root_.GlobalTheory.CuspGeneric.avg_equiv (G₂ × G₁) (G₁ × G₂) (Γ₂.prod Γ₁) (Γ₁.prod Γ₂) (isCoLat_prod h₂ h₁) (isCoLat_prod h₁ h₂) (swapEquiv G₁ G₂)
    (fun x => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩) Φ hΦ
  exact a.symm.trans (c.symm.trans b)

end General

theorem avg_comm (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ]
    (Φ : (ι → Ad E) × (κ → Ad E) → ℂ) (hΦ : Per ((ratV E ι).prod (ratV E κ)) Φ) :
    avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (x, y))) =
      avg (ratV E κ) (fun y => avg (ratV E ι) (fun x => Φ (x, y))) :=
  avg_comm_of_isCoLat (isCoLat_ratV E ι) (isCoLat_ratV E κ) Φ hΦ

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageSumIndexFubini
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

def sumArrowAddHomeo (A ι κ : Type) [AddCommGroup A] [TopologicalSpace A] :
    ((ι → A) × (κ → A)) ≃ₜ+ (ι ⊕ κ → A) where
  toFun p := Sum.elim p.1 p.2
  invFun f := (fun i => f (Sum.inl i), fun j => f (Sum.inr j))
  left_inv _ := rfl
  right_inv f := by ext (i | j) <;> rfl
  map_add' p q := by ext (i | j) <;> rfl
  continuous_toFun := by
    refine continuous_pi fun s => ?_
    rcases s with i | j
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply j).comp continuous_snd
  continuous_invFun :=
    (continuous_pi fun i => continuous_apply _).prodMk (continuous_pi fun j => continuous_apply _)

theorem sum_elim_mem_ratV (E : Type) [Field E] [NumberField E] (ι κ : Type) (x : ι → Ad E) (y : κ → Ad E) :
    Sum.elim x y ∈ ratV E (ι ⊕ κ) ↔ x ∈ ratV E ι ∧ y ∈ ratV E κ := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨⟨fun i => c (Sum.inl i), funext fun i => congrFun hc (Sum.inl i)⟩,
      ⟨fun j => c (Sum.inr j), funext fun j => congrFun hc (Sum.inr j)⟩⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    refine ⟨Sum.elim c d, funext fun s => ?_⟩
    rcases s with i | j <;> rfl

theorem avg_sum_index : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ]
    (Φ : (ι ⊕ κ → Ad E) → ℂ), Per (ratV E (ι ⊕ κ)) Φ →
    avg (ratV E (ι ⊕ κ)) Φ = avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (Sum.elim x y))) := by
  intro E _ _ ι κ _ _ Φ hΦ
  have hι := isCoLat_ratV E ι
  have hκ := isCoLat_ratV E κ
  have hs := isCoLat_ratV E (ι ⊕ κ)
  have hp : IsCoLat ((ratV E ι).prod (ratV E κ)) := by
    obtain ⟨d₁, K₁, hK₁, c₁⟩ := hι
    obtain ⟨d₂, K₂, hK₂, c₂⟩ := hκ
    refine ⟨?_, K₁ ×ˢ K₂, hK₁.prod hK₂, fun x => ?_⟩
    · let f : ↥((ratV E ι).prod (ratV E κ)) → ratV E ι × ratV E κ := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      have hf : Continuous f :=
        (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _)
      refine DiscreteTopology.of_continuous_injective hf fun p q h => ?_
      have e₁ := congrArg (fun r => (r.1 : ι → Ad E)) h
      have e₂ := congrArg (fun r => (r.2 : κ → Ad E)) h
      exact Subtype.ext (Prod.ext e₁ e₂)
    · obtain ⟨γ₁, m₁, k₁⟩ := c₁ x.1
      obtain ⟨γ₂, m₂, k₂⟩ := c₂ x.2
      exact ⟨(γ₁, γ₂), ⟨m₁, m₂⟩, k₁, k₂⟩
  let e := sumArrowAddHomeo (Ad E) ι κ
  have he : ∀ p, e p ∈ ratV E (ι ⊕ κ) ↔ p ∈ (ratV E ι).prod (ratV E κ) := fun p =>
    (sum_elim_mem_ratV E ι κ p.1 p.2).trans AddSubgroup.mem_prod.symm
  have hper : Per ((ratV E ι).prod (ratV E κ)) (fun p => Φ (e p)) := by
    refine ⟨hΦ.1.comp e.continuous_toFun, fun γ hγ x => ?_⟩
    have : e (γ + x) = e γ + e x := map_add e γ x
    simp only [this]
    exact hΦ.2 _ ((he γ).2 hγ) _
  have h1 := _root_.GlobalTheory.CuspGeneric.avg_equiv _ _ _ _ hp hs e he Φ hΦ
  have h2 := GlobalTheory.T.quotientAverage_prod_fubini _ _ _ _ hι hκ _ hper
  rw [← h1, h2]
  rfl

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConst
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem stInv_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l)
    (x : Bst P), (∀ g : ↥(GK K), actSt P (g : GQ l) x = x) ↔
      ∃ c : ↥(K0 K), x = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
  intro l _ P AI T K x
  constructor
  · intro h
    obtain ⟨hdom, h2, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
    haveI := hdom
    obtain ⟨c, hcK, hc⟩ := h2 K 1 x one_ne_zero fun g => by rw [map_one, h g, one_mul]
    have hmem : (c : Om l) ∈ K0 K := IntermediateField.mem_inf.2 ⟨hcK, c.2⟩
    refine ⟨⟨c, hmem⟩, ?_⟩
    rw [hc, mul_one, Polynomial.algebraMap_apply]
    rfl
  · rintro ⟨c, rfl⟩ g
    have hc : (c : Om l) ∈ (K.1 : IntermediateField ℚ_[l] (Om l)) := (IntermediateField.mem_inf.1 c.2).1
    have hg : (g : GQ l) (c : Om l) = (c : Om l) := (mem_fixingSubgroup_iff _).1 g.2 _ hc
    have hK0 : algebraMap ↥(K0 K) P.R.B c =
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, (IntermediateField.mem_inf.1 c.2).2⟩ := rfl
    rw [actSt]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, stHom_apply, Polynomial.map_C, Polynomial.C_comp]
    congr 1
    rw [hK0]
    exact P.actQ_Kur _ _ _ hg

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLaw
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem colT_blkU_mul : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → ∀ (y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (g : GA E a),
      colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a (m + 1)) y) * colT ψ (m + 1) f g := by
  intro E _ _ a ψ hψ m f hf y g
  have hper := per_coef (a := a) hψ (eLast a (m + 1)) hf.cont
    (fun c g' => hf.left _ (isMir_blkU c) g') g
  have hT := GlobalTheory.T.quotientAverage_translate_invariant (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) _ hper y
  have hpt : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E =>
        ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) =
      fun x => ψ (dot (eLast a (m + 1)) y) *
        (ψ (-dot (eLast a (m + 1)) (x + y)) * f (blkU (x + y) * g)) := by
    funext x
    have hd : dot (eLast a (m + 1)) (x + y) = dot (eLast a (m + 1)) x + dot (eLast a (m + 1)) y := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hu : (blkU (x + y) : GA E a) = blkU x * blkU y := posU_add _ x y
    have h1 : ψ (dot (eLast a (m + 1)) y) * ψ (-dot (eLast a (m + 1)) y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hd, hu, neg_add, AddChar.map_add_eq_mul, mul_assoc (blkU x)]
    calc ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))
        = (ψ (dot (eLast a (m + 1)) y) * ψ (-dot (eLast a (m + 1)) y)) *
            (ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) := by rw [h1, one_mul]
      _ = _ := by ring
  change avg _ (fun x => ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) =
    _ * avg _ (fun x => ψ (-dot (eLast a (m + 1)) x) * f (blkU x * g))
  rw [hpt, avg_const_mul]
  exact congrArg _ hT

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformMirabolicInvari
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem IsMir.succ {E : Type} [Field E] {a m : ℕ} {γ : GL (Fin a) E} (hγ : IsMir m γ) : IsMir (m + 1) γ :=
  fun i k h => hγ i k (by omega)

theorem colT_isMir_invariant : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ γ : GL (Fin a) E, IsMir m γ →
    ∀ g, colT ψ (m + 1) f (ratGL E a γ * g) = colT ψ (m + 1) f g := by
  intro E _ _ a ψ hψ m f hma hf γ hγ g
  have key := _root_.GlobalTheory.CuspGeneric.coefF_ratGL_mul E a ψ hψ m f hf.cont hf.left γ hγ.succ (eLast a (m + 1)) g
  unfold colT
  rw [key]
  congr 1
  funext t
  let s0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hma⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
  rw [Finset.sum_eq_single s0]
  · have h1 : eLast (E := E) a (m + 1) s0 = 1 := by simp [eLast, s0]
    rw [h1, one_mul, hγ _ _ (Or.inl (le_refl m))]
    have ht := t.2.1
    simp only [eLast, Matrix.one_apply]
    by_cases h : (t.1.1 : ℕ) = m
    · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
    · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
  · intro s _ hs
    have h0 : eLast (E := E) a (m + 1) s = 0 := by
      simp only [eLast]
      rw [if_neg]
      intro e
      apply hs
      have h2 := s.2.2
      apply Subtype.ext
      exact Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformNeZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem colT_ne_zero_of_good : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → f ≠ 0 → colT ψ (m + 1) f ≠ 0 := by
  intro E _ _ a ψ hψ m f hma hG hf
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, f g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (funext h)
  have hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀)) :=
    per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀
  have hΦ0 : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) ≠ 0 := by
    intro h
    have h1 := congrFun h 0
    simp only [Pi.zero_apply] at h1
    apply hg₀
    have e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1 := posU_zero _
    rw [e, one_mul] at h1
    exact h1
  obtain ⟨ξ, hξ⟩ : ∃ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, coefF ψ (m + 1) ξ f g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΦ0 (_root_.GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero E _ ψ hψ _ hPer h)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply hξ
    have hv := hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀
    have e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E, ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := by
      intro x
      simp [dot]
    simp only [coefF, e, one_mul]
    exact hv
  obtain ⟨γ, hγ, hγξ⟩ := _root_.GlobalTheory.CuspGeneric.mir_exists_row E a m hma ξ hξ0
  intro h
  apply hξ
  have h1 := congrFun h (ratGL E a γ * g₀)
  simp only [Pi.zero_apply, colT] at h1
  rw [_root_.GlobalTheory.CuspGeneric.coefF_ratGL_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀] at h1
  have e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ :=
    funext hγξ
  rw [e] at h1
  exact h1

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRecStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → ReciprocityTheory.ChartRestriction.T2.VhE := by
  first | exact @GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity | exact GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity | (intros; apply GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachLatticeTrivialModUniformizer


set_option maxHeartbeats 1000000 in
theorem wachLattice_galois_trivial_mod_uniformizer : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P2 D HW F := by
  intro D HW F Cm l _ K s LL h T hT
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.NL.GamModX.gam_mod_π_mod_X D HW F Cm l K s LL h T hT
  refine ⟨(wach_gamma_stable_first _ T).1, (wach_gamma_stable_first _ T).2, fun x hx => ?_⟩
  obtain ⟨y, hy, e⟩ := h3 x hx
  exact ⟨y, hy, e.symm⟩

end GlobalTheory.NL.WachLatticeTrivialModUniformizer
end

