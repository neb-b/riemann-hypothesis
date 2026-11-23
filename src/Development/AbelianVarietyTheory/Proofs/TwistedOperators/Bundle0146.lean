module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

variable {D : D7}

def Stab (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) : Prop :=
  g ∈ GfC V ∧ finE V g ∈ St β

def UnrOff (b : AE D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → b * (x : AE D) = b → χ x = 1


open Classical in
def adjDatum (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (Pg Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (a : AE D) (x : WO S T) : ℂ :=
  if IsHalf a x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
      omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
  else 0

theorem finE_val (V : HSp D) (g : GA D V) :
    (finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl

theorem Stab.one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) : Stab V β 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩

theorem Stab.inv {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (h : Stab V β g) : Stab V β g⁻¹ :=
  ⟨Subgroup.inv_mem _ h.1, by rw [map_inv]; exact Subgroup.inv_mem _ h.2⟩

theorem isFrame_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hx : x ∈ St β) : IsFrame (x * β) Λ := by
  obtain ⟨y, rfl⟩ := hx
  have e : frGL β y * β = β * intGL F E n y := by simp [frGL]
  have key : ∀ (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      (∀ i, w i ∈ Formalism.L2.Herm.intAf F E) →
      ∀ i, (intGL F E n z).val.mulVec w i ∈ Formalism.L2.Herm.intAf F E := fun z w hw i => by
    show ∑ j, ((z.val i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * w j ∈ _
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (z.val i j).2 (hw j)
  intro w
  rw [hβ w, e, mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv]
  refine ⟨fun h => key _ _ h, fun h => ?_⟩
  have := key y _ h
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at this

theorem mem_latO_iff {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Lev.EAf D)}
    {βT : GL (Fin T.rank) (Lev.EAf D)} (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) {g : GA D S} {h : GA D T}
    (hg : finE S g ∈ St βS) (hh : finE T h ∈ St βT) (u : WO S T) :
    u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have key : ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ u,
      u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) →
      actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
    fun g h hg hh u hu => GlobalTheory.AdelicLatMove.actO_mem_latO S T g h ΛS ΛS ΛT ΛT βS _ βT _ hS (isFrame_mul hS hg) hT
      (isFrame_mul hT hh) rfl rfl u hu
  refine ⟨key g h hg hh u, fun hu => ?_⟩
  have := key g⁻¹ h⁻¹ (by rw [map_inv]; exact inv_mem hg) (by rw [map_inv]; exact inv_mem hh) _ hu
  have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at e
  rwa [e] at this

theorem exists_det_int {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β) :
    ∃ a : Formalism.L2.Herm.intAf D.host.F D.host.E, (a : Lev.EAf D) = toEAf D (Formalism.L2.Theta.mt V g).det ∧
      ∀ PP : Pl D.host.E, ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) =
        resS D.host.F PP a := by
  obtain ⟨y, hy⟩ := hg
  refine ⟨y.val.det, ?_, fun PP => ?_⟩
  · have h1 : toEAf D (Formalism.L2.Theta.mt V g).det = (finE V g).val.det := by
      rw [finE_val, RingHom.map_det]; rfl
    have h2 : (Matrix.GeneralLinearGroup.det (frGL β y)) = Matrix.GeneralLinearGroup.det (intGL _ _ _ y) := by
      simp [frGL]
    have h3 := congrArg Units.val h2
    rw [h1, ← hy]
    refine Eq.trans ?_ h3.symm
    exact (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.map_det y.val
  · rw [← hy, redFn_frGL]
    exact ((resS D.host.F PP).map_det y.val).symm

def detAt (e : AE D) (he : e * e = e) (V : HSp D) : GA D V →* (AE D)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => e * (Formalism.L2.Theta.mt V g).det + (1 - e)
      map_one' := by rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]; ring
      map_mul' := fun g g' => by
        rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.det_mul]
        linear_combination (-(Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g').det + (Formalism.L2.Theta.mt V g).det
          + (Formalism.L2.Theta.mt V g').det - 1) * he }

theorem isDetAt_detAt (e : AE D) (he : e * e = e) (V : HSp D) (g : GA D V) : IsDetAt e V g (detAt e he V g) := rfl

end GlobalTheory.VecInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlAdaptedBasisMonotoneSubspaceChain
section
open scoped Matrix

namespace GlobalTheory.Flag

theorem exists_sup_eq_finrank_sub {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {A B : Submodule K V} (hAB : A ≤ B) :
    ∃ C : Submodule K V, C ⊔ A = B ∧
      Module.finrank K C = Module.finrank K B - Module.finrank K A := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl A
  have hsup : q ⊓ B ⊔ A = B := by
    rw [inf_comm, inf_sup_assoc_of_le _ hAB, sup_comm, hq.sup_eq_top, inf_top_eq]
  refine ⟨q ⊓ B, hsup, ?_⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (q ⊓ B) A
  have h2 : q ⊓ B ⊓ A = ⊥ := by
    refine eq_bot_iff.2 (le_trans ?_ hq.inf_eq_bot.le)
    rw [inf_comm A q]; exact inf_le_inf_right _ inf_le_left
  rw [hsup, h2, finrank_bot] at h1
  omega

theorem exists_gl_adapted_chain : ∀ {K : Type} [Field K] {n m : ℕ} (Y : Fin (m + 1) → Submodule K (Fin n → K)), Monotone Y → Y 0 = ⊥ → Y (Fin.last m) = ⊤ →
    ∃ (d : Fin m → ℕ) (h : ∑ j, d j = n) (g : GL (Fin n) K), ∀ (j : Fin (m + 1)) (y : Fin n → K),
      y ∈ Y j ↔ ∀ i : Fin n, (j : ℕ) ≤ ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) i : Fin m) : ℕ) →
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) i = 0 := by
  intro K _ n m Y hmono h0 htop
  let r : Fin (m + 1) → ℕ := fun j => Module.finrank K (Y j)
  have hC : ∀ j : Fin m, ∃ C : Submodule K (Fin n → K), C ⊔ Y j.castSucc = Y j.succ ∧
      Module.finrank K C = r j.succ - r j.castSucc :=
    fun j => exists_sup_eq_finrank_sub (hmono (Fin.castSucc_le_succ j))
  choose C hCsup hCrk using hC
  let d : Fin m → ℕ := fun j => r j.succ - r j.castSucc
  let R : ℕ → ℕ := fun k => r ⟨min k m, by omega⟩
  have hRmono : Monotone R := by
    intro a b hab
    exact Submodule.finrank_mono (hmono (Fin.mk_le_mk.2 (min_le_min_right m hab)))
  have hsum : ∑ j, d j = n := by
    have e1 : ∑ j, d j = ∑ k ∈ Finset.range m, (R (k + 1) - R k) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      have a1 : (⟨min ((j : ℕ) + 1) m, by omega⟩ : Fin (m + 1)) = j.succ := Fin.ext (by simp)
      have a2 : (⟨min (j : ℕ) m, by omega⟩ : Fin (m + 1)) = j.castSucc := Fin.ext (by simp)
      simp only [d, R, a1, a2]
    rw [e1, Finset.sum_range_tsub hRmono]
    have a3 : (⟨min m m, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
    have a4 : (⟨min 0 m, by omega⟩ : Fin (m + 1)) = 0 := Fin.ext (by simp)
    have hRm : R m = n := by
      show Module.finrank K (Y ⟨min m m, _⟩) = n
      rw [a3, htop, finrank_top, Module.finrank_fin_fun]
    have hR0 : R 0 = 0 := by
      show Module.finrank K (Y ⟨min 0 m, _⟩) = 0
      rw [a4, h0, finrank_bot]
    rw [hRm, hR0, Nat.sub_zero]
  let B : ∀ j : Fin m, Module.Basis (Fin (d j)) K (C j) := fun j => Module.finBasisOfFinrankEq K (C j) (hCrk j)
  let f : (Σ j : Fin m, Fin (d j)) → (Fin n → K) := fun p => (B p.1 p.2 : Fin n → K)
  have hspanC : ∀ j : Fin m, Submodule.span K (Set.range fun i => f ⟨j, i⟩) = C j := by
    intro j
    have : (Set.range fun i => f ⟨j, i⟩) = (C j).subtype '' Set.range (B j) :=
      Set.range_comp (C j).subtype (B j)
    rw [this, Submodule.span_image, (B j).span_eq, Submodule.map_subtype_top]
  have hspan : ∀ k (hk : k ≤ m), Y ⟨k, by omega⟩ = Submodule.span K (f '' {p | (p.1 : ℕ) < k}) := by
    intro k
    induction k with
    | zero => intro _; simp [h0]
    | succ k ih =>
      intro hk
      have hset : f '' {p | (p.1 : ℕ) < k + 1} =
          (Set.range fun i => f ⟨⟨k, hk⟩, i⟩) ∪ f '' {p | (p.1 : ℕ) < k} := by
        ext v
        constructor
        · rintro ⟨⟨a, i⟩, hp, rfl⟩
          simp only [Set.mem_setOf_eq] at hp
          by_cases ha : (a : ℕ) < k
          · exact Or.inr ⟨⟨a, i⟩, ha, rfl⟩
          · obtain rfl : a = ⟨k, hk⟩ := Fin.ext (by simp; omega)
            exact Or.inl ⟨i, rfl⟩
        · rintro (⟨i, rfl⟩ | ⟨p, hp, rfl⟩)
          · exact ⟨⟨⟨k, hk⟩, i⟩, by simp, rfl⟩
          · exact ⟨p, by simp only [Set.mem_setOf_eq] at hp ⊢; omega, rfl⟩
      have e1 : (⟨k + 1, by omega⟩ : Fin (m + 1)) = (⟨k, hk⟩ : Fin m).succ := rfl
      have e2 : (⟨k, by omega⟩ : Fin (m + 1)) = (⟨k, hk⟩ : Fin m).castSucc := rfl
      rw [hset, Submodule.span_union, hspanC, ← ih (by omega), e1, e2, hCsup]
  let b : Fin n → (Fin n → K) := fun i => f ((GlobalTheory.SmGL.stdBlocks d hsum).symm i)
  have hsub : ∀ j : Fin (m + 1), f '' {p | (p.1 : ℕ) < j} = b '' {i | ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d hsum) i : Fin m) : ℕ) < j} := by
    intro j
    ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(GlobalTheory.SmGL.stdBlocks d hsum) p, by simpa [GlobalTheory.SmGL.blk] using hp, by simp [b]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(GlobalTheory.SmGL.stdBlocks d hsum).symm i, hi, rfl⟩
  have htopb : ⊤ ≤ Submodule.span K (Set.range b) := by
    have h1 := hspan m le_rfl
    have h2 : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
    have h3 := hsub (Fin.last m)
    rw [Fin.val_last] at h3
    rw [h2, htop, h3] at h1
    rw [h1]
    exact Submodule.span_mono (Set.image_subset_range _ _)
  have hli : LinearIndependent K b := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, top_unique htopb, finrank_top]
    simp
  let Bas : Module.Basis (Fin n) K (Fin n → K) := Module.Basis.mk hli htopb
  have hBas : ⇑Bas = b := Module.Basis.coe_mk hli htopb
  let pf := Pi.basisFun K (Fin n)
  let g : GL (Fin n) K := ⟨pf.toMatrix Bas, Bas.toMatrix pf, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  have hg : ∀ y : Fin n → K, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y = ⇑(Bas.repr y) := by
    intro y
    have := Module.Basis.toMatrix_mulVec_repr pf Bas y
    have hy : ⇑(pf.repr y) = y := funext fun i => by simp [pf]
    rw [hy] at this
    exact this
  refine ⟨d, hsum, g, fun j y => ?_⟩
  have hYj : Y j = Submodule.span K (Bas '' {i | ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d hsum) i : Fin m) : ℕ) < j}) := by
    rw [hBas, ← hsub, ← hspan j (by omega)]
  rw [hYj, Module.Basis.mem_span_image, hg]
  constructor
  · intro hs i hi
    by_contra hne
    have := hs (Finsupp.mem_support_iff.2 hne)
    simp only [Set.mem_setOf_eq] at this
    omega
  · intro H i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    by_contra hlt
    simp only [Set.mem_setOf_eq, not_lt] at hlt
    exact hi (H i hlt)

end GlobalTheory.Flag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeTranslateOfMemSpanFixedTranslates
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.AvgHecke

open GlobalTheory.PRep

theorem exists_hecke_of_mem_span : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (s w : M), (∀ k ∈ K, ρ k s = s) → (∀ k ∈ K, ρ k w = w) → w ∈ Submodule.span ℂ (Set.range fun g => ρ g s) → ∃ h ∈ Hecke ℂ K, heckeVec ρ K h s = w := by
  classical
  intro G _ K hK M _ _ ρ s w hs hw hspan
  have hx : s ∈ fixed ρ K := GlobalTheory.LGrp.mem_fixed.2 hs
  have hy : w ∈ fixed ρ K := GlobalTheory.LGrp.mem_fixed.2 hw
  have hr : w ∈ LinearMap.range (GlobalTheory.LFun.HeckeScalar.orbitMap ρ K s) := by
    refine Submodule.span_le.2 ?_ hspan
    rintro _ ⟨g, rfl⟩
    exact ⟨Finsupp.single (g : G ⧸ K) 1, by rw [GlobalTheory.LFun.HeckeScalar.orbitMap_single hx, one_smul]⟩
  obtain ⟨φ, rfl⟩ := hr
  obtain ⟨ψ, hψ, e⟩ := GlobalTheory.LFun.HeckeScalar.exists_fixed_preimage _ (GlobalTheory.LFun.HeckeScalar.orbitMap_permRep hx)
    (GlobalTheory.LFun.HeckeScalar.mem_finOrbit hK φ) hy
  refine ⟨fun g => ψ g, ⟨fun a b g => ?_, ψ.support.image Quotient.out, fun g hg => ?_⟩, ?_⟩
  · have := GlobalTheory.LFun.HeckeScalar.permRep_apply (a : G) ψ (g : G ⧸ K)
    rw [GlobalTheory.LGrp.mem_fixed.1 hψ _ a.2] at this
    simpa using this
  · obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨_, Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hg), 1, j⁻¹, by simp [hj]⟩
  · rw [← e, heckeVec, GlobalTheory.LFun.HeckeScalar.orbitMap, Finsupp.linearCombination_apply, Finsupp.sum,
      finsum_eq_sum_of_support_subset (s := ψ.support)]
    · simp
    · intro c hc
      by_contra h
      exact hc (by simp [Finsupp.notMem_support_iff.1 h])

end GlobalTheory.SphTheta.AvgHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergInvariantLinearFormIsotropicVacu
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

theorem exists_linearForm_invariant_isotropic_vacuum : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ A : Submodule R X, (∀ a ∈ A, ∀ b ∈ A, γ a b = 1) → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ ∀ a ∈ A, ∀ v, ℓ (W a v) = ℓ v := by
  intro R X M _ _ _ _ _ σ w γ W h Λ hΛ s hs hfix hspan A hA
  have key : ∀ z y, y - z ∈ Λ → W z s = γ (w • z) (y - z) • W y s := by
    intro z y hyz
    have h1 := h.comp z (y - z) s
    rwa [hfix _ hyz, add_sub_cancel] at h1
  let P : X ⧸ Λ → Prop := fun q => ∃ a ∈ A, (Submodule.Quotient.mk a : X ⧸ Λ) = q
  let rep : X ⧸ Λ → X := fun q => if hq : P q then hq.choose else Quotient.out q
  have hrep : ∀ q, (Submodule.Quotient.mk (rep q) : X ⧸ Λ) = q := by
    intro q
    by_cases hq : P q
    · simp only [rep, dif_pos hq]; exact hq.choose_spec.2
    · simp only [rep, dif_neg hq]; exact Quotient.out_eq q
  have hrepA : ∀ q, P q → rep q ∈ A := by
    intro q hq
    simp only [rep, dif_pos hq]; exact hq.choose_spec.1
  let e : X ⧸ Λ → M := fun q => W (rep q) s
  have he : ∀ z, W z s = γ (w • z) (rep (Submodule.Quotient.mk z) - z) • e (Submodule.Quotient.mk z) := by
    intro z
    exact key z _ ((Submodule.Quotient.eq Λ).1 (hrep _))
  have hli : LinearIndependent ℂ e := by
    refine linearIndependent_of_simultaneous_eigen e (fun q (l : Λ) => γ l (rep q)) (fun l : Λ => W l) ?_ ?_ ?_
    · intro q q' hq
      have hm : rep q - rep q' ∈ Λ := by
        rw [hΛ]
        intro a ha
        apply h.swap_eq_one
        have h1 : γ a (rep q) = γ a (rep q') := congrFun hq ⟨a, ha⟩
        rw [sub_eq_add_neg, h.add_right, h.neg_right, h1, mul_inv_cancel₀ (h.ne_zero _ _)]
      rw [← hrep q, ← hrep q']
      exact (Submodule.Quotient.eq Λ).2 hm
    · intro l q
      show W l (W (rep q) s) = γ l (rep q) • W (rep q) s
      rw [h.comm, hfix l l.2]
    · intro q h0
      have h1 := h.neg_comp (rep q) s
      rw [show W (rep q) s = 0 from h0, map_zero] at h1
      exact hs ((smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _))
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    show W z s ∈ _
    rw [he z]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  let b := Module.Basis.mk hli hsp
  let ℓ : M →ₗ[ℂ] ℂ := b.constr ℂ (fun q => if P q then (1 : ℂ) else 0)
  have hℓ : ∀ q, ℓ (e q) = if P q then (1 : ℂ) else 0 := by
    intro q
    have := b.constr_basis ℂ (fun q => if P q then (1 : ℂ) else 0) q
    rwa [Module.Basis.mk_apply] at this
  have hwA : ∀ a ∈ A, ∀ b ∈ A, γ (w • a) b = 1 := fun a ha b hb => hA _ (A.smul_mem w ha) b hb
  refine ⟨ℓ, ?_, ?_⟩
  · have h0 : P (Submodule.Quotient.mk 0) := ⟨0, A.zero_mem, rfl⟩
    have h1 := he 0
    rw [h.zero, hwA 0 A.zero_mem _ (A.sub_mem (hrepA _ h0) A.zero_mem), one_smul] at h1
    rw [h1, hℓ, if_pos h0]
  · intro a ha v
    have hext : ℓ ∘ₗ W a = ℓ := by
      refine b.ext fun q => ?_
      rw [Module.Basis.mk_apply, LinearMap.comp_apply]
      show ℓ (W a (W (rep q) s)) = ℓ (e q)
      rw [h.comp, he (a + rep q), map_smul, map_smul, hℓ, hℓ]
      by_cases hq : P q
      · have hA1 : a + rep q ∈ A := A.add_mem ha (hrepA q hq)
        have hq' : P (Submodule.Quotient.mk (a + rep q)) := ⟨_, hA1, rfl⟩
        rw [if_pos hq, if_pos hq', hwA a ha _ (hrepA q hq), hwA _ hA1 _ (A.sub_mem (hrepA _ hq') hA1)]
        simp
      · have hq' : ¬ P (Submodule.Quotient.mk (a + rep q)) := by
          rintro ⟨c, hc, hce⟩
          apply hq
          refine ⟨c - a, A.sub_mem hc ha, ?_⟩
          rw [Submodule.Quotient.mk_sub, hce, ← Submodule.Quotient.mk_sub, add_sub_cancel_left, hrep]
        rw [if_neg hq, if_neg hq']
        simp
    exact LinearMap.congr_fun hext v

end GlobalTheory.SphTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzArchimedeanSliceAdelicSchwartz
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchSlice

theorem exists_schwartz_slice : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, ∃ g : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
    g t = Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)) := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g 0 • f, fun t => ?_⟩
    simp only [SchwartzMap.smul_apply, smul_eq_mul, pureA, RingEquiv.apply_symm_apply]
    rw [mul_comm]
    rfl
  | zero => exact ⟨0, fun t => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁⟩ := hx
    obtain ⟨g₂, h₂⟩ := hy
    exact ⟨g₁ + g₂, fun t => by rw [SchwartzMap.add_apply, h₁, h₂]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨g₁, h₁⟩ := hx
    exact ⟨c • g₁, fun t => by rw [SchwartzMap.smul_apply, h₁]; rfl⟩

end GlobalTheory.ArchSlice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnramifiedExponentOfIwahoriFixedVector
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL

theorem exists_expMult_ne_zero_of_fixed_iwahori (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsAdmissible π)
    (h : fixed π (iwahori k (Fin n)) ≠ ⊥) : ∃ χ : (Fin n → kˣ) →* ℂˣ, expMult π χ ≠ 0 := by
  haveI := hπ.2 _ (IwahoriOnto.isOpen_iwahori k (Fin n)) (IwahoriOnto.isCompact_iwahori k (Fin n))
  have hb := GlobalTheory.Published.BorelCasselman_holds k (Fin n) V π hπ
  haveI : FiniteDimensional ℂ (fixed (jacBU π) (torusO k (Fin n))) :=
    Module.Finite.of_surjective _ hb.2
  haveI : Nontrivial (fixed π (iwahori k (Fin n))) := Submodule.nontrivial_iff_ne_bot.2 h
  haveI : Nontrivial (fixed (jacBU π) (torusO k (Fin n))) := hb.1.nontrivial
  obtain ⟨ψ, v, hv, hψ⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ (Fin n → kˣ) _
    (jacBUFixed π) fun a b => by rw [← map_mul, mul_comm, map_mul]
  let ι : (ofChar ψ).IntertwiningMap (jacBUFixed π) :=
    ⟨LinearMap.toSpanSingleton ℂ _ v, fun g => by
      refine LinearMap.ext_ring ?_
      simp [hψ]⟩
  exact ⟨ψ, JHMult.jhMult_ne_zero_iff.2 (IsSubquotient.of_injective ι (smul_left_injective ℂ hv))⟩

end GlobalTheory.SmGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
section
noncomputable section

namespace GlobalTheory.CoinvKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

def IsStabW (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  N ≤ A ∧ (∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N) ∧
    (∀ k ∈ KInf σ W emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N) ∧
    ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def HasRelY (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  (∀ v : Pl F, ∀ g ∈ UAt σ Y (evFin F v), ∀ Φ ∈ A, om (g, 1) Φ - Φ ∈ N) ∧
    (∀ k ∈ KInf σ Y emb, ∀ Φ ∈ A, om (k, 1) Φ - Φ ∈ N) ∧
    ∀ γ ∈ Lines σ Y, ∀ Φ ∈ A, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def IsThetaSub (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  IsStabW om emb A N ∧ HasRelY om emb A N

end GlobalTheory.CoinvKer

end
end

