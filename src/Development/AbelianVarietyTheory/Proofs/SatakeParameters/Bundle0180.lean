module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentLevelNilpotent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartForm
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

open GlobalTheory.DefU

namespace GlobalTheory.Cong

theorem ofType_of_finPart_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n)
    (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) →
    OfType (fun τ => W.at τ) K π.V := by
  intro E _ _ _ n π W K f hf hf0 hK
  refine ⟨π.isAut, fun τ => ?_, ?_⟩
  · have h : (AU.mk π).HasWt (InfinitePlace.mk τ).embedding (W (InfinitePlace.mk τ)) :=
      hasWeightAt_of_finPart π W hf hf0 (InfinitePlace.mk τ)
    rcases InfinitePlace.embedding_mk_eq τ with e | e
    · have h' := h
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), e] at h'
      exact h'
    · have h2 := h.conjugate
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ] at h2
      exact h2
  · have hne : f.1 ≠ 0 := fun h => hf0 (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v, f.1 v ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (LinearMap.ext hc)
    refine ⟨f.1 v, AutSub.mem_finPart.1 hf v, hv, fun x hx => ?_⟩
    funext g
    rw [RU_apply]
    exact hK x hx v g

end GlobalTheory.Cong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralOffPrimesMatrixStepEntryData
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.KerTie

theorem intOff_pow' {S : Finset ℕ} {z : ℂ} (h : IntOff S z) (n : ℕ) : IntOff S (z ^ n) := by
  induction n with
  | zero => simpa using IntOff.one
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem intOff_prod' {S : Finset ℕ} {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, IntOff S (f k)) :
    IntOff S (∏ k ∈ s, f k) :=
  Finset.prod_induction _ (IntOff S) (fun _ _ ha hb => ha.mul hb) IntOff.one h

theorem intAt_chArg_of_omPhi {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu)
    {y : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))}
    (h0 : omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) y ≠ 0) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * -Loc.chArg y) := by
  have hm := hL.hm
  by_cases hP : P.1 ∈ Pr.vGs
  · have h1 := (GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type Ch sel mu cst i P (by omega) hP _ _ (hL.stabG i al P hP)
      (hL.stabG (i + 1) be P hP)).2 y h0
    rw [hL.depthG P hP, pow_one, mul_neg]
    exact GlobalTheory.TopStep.intAt_neg h1
  · have h1 := right_ne_zero_of_mul h0
    rw [PhiAt, if_neg hP] at h1
    have hb := hL.boundQ i al P hP
    have hb' := hL.boundQ (i + 1) be P hP
    have hD := hL.depthQ' P hP
    simp only [lamYat, hP, if_false, GlobalTheory.GO.ChRoot.mem_lamY_zero] at hb hb'
    have hint : IntAt P.1 ((qOf P.1 : X.E) ^ (i + 1) * Loc.chArg y) := by
      refine GlobalTheory.ColPeriod.EntQ.intAt_chArg _ y fun v hv => ?_
      have h2 := (hb' _ (GlobalTheory.ColPeriod.EntQ.int_of_PhiQ (GlobalTheory.ColPeriod.EntQ.k_le_N R _) (GlobalTheory.ColPeriod.EntQ.k_le_N R _) h1 (hb v hv).1)).2
      have h3 : (L.h i al P) ((L.h i al P)⁻¹ v) = v := LinearEquiv.apply_symm_apply _ v
      simpa [h3] using h2
    obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + (i + 1) := ⟨cst.D P - (i + 1), by omega⟩
    rw [hd, pow_add, mul_neg, mul_assoc]
    exact GlobalTheory.TopStep.intAt_neg ((GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _).mul hint)

theorem intOff_xiEntry : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < t.m2 → ∀ al be p p' x, IntOff (t.O u μ).S (t.seam.σ₀ (XiEntry (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i al be p p' x)) := by
  intro D L hT Gi Gl K Y cX ex t hmu hval u μ hg i hi al be p p' x
  have hL := t.idx_ok μ
  have hm := hL.hm
  unfold XiEntry
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod' _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using IntOff.one
    · simpa using IntOff.zero
  · have hq := GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P
    have hst : P.1 ∈ t.Pr.vGs → (t.idx μ).h i al P ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) i P.1) ∧
        (t.idx μ).h (i + 1) be P ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) (i + 1) P.1) :=
      fun hP => ⟨hL.stabG i al P hP, hL.stabG (i + 1) be P hP⟩

    have hom : ∀ y, IntOff (t.O u μ).S (t.seam.σ₀ (omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P
        ((t.idx μ).h i al P) ((t.idx μ).h (i + 1) be P) y)) := fun y =>
      GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t hmu hval u μ hg i (by omega) P _ _ hst y
    unfold XiAt E1at Loc.E1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_mul, map_sum]
    refine IntOff.mul (GlobalTheory.UnipVol.intOff_volN_Cbe D L hT Gi Gl K Y cX ex t u μ i P _) (IntOff.mul ?_ (IntOff.sum _ _ fun s _ => ?_))
    · rw [map_pow, map_inv₀, map_pow, map_natCast, ← inv_pow]
      exact intOff_pow' (intOff_pow' (IntOff.inv_nat hq) _) _
    · generalize Loc.xx1 _ s = y
      by_cases h0 : omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P ((t.idx μ).h i al P) ((t.idx μ).h (i + 1) be P) y = 0
      · rw [h0, zero_mul, map_zero]
        exact IntOff.zero
      · rw [map_mul]
        refine (hom _).mul (IntOff.of_pow (n := qOf P.1 ^ (t.cst μ).D P) (pow_pos (GlobalTheory.GO.ChRoot.qOf_pos _) _) ?_)
        rw [← map_pow, GlobalTheory.GO.ChRoot.psi_root hL.cst_ok P _ (intAt_chArg_of_omPhi hL hi al be P h0), map_one]

end GlobalTheory.KerTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOfFinOrderOfCompactConjMemUnitaryRationalPoint
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory

theorem isOfFinOrder_of_conj_mem_ratU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Subgroup (UA E n)),
    IsCompact (D : Set (UA E n)) → ∀ (g : UA E n), ∀ c ∈ D, g * c * g⁻¹ ∈ ratU E n → IsOfFinOrder c := by
  intro E _ _ _ n D hD g c hc hgc
  haveI : T1Space (GA E n) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  haveI : DiscreteTopology (ratGL E n).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n
  have hcl : IsClosed (((ratGL E n).range : Subgroup (GA E n)) : Set (GA E n)) := Subgroup.isClosed_of_discrete
  let K : Set (GA E n) := (fun x : UA E n => ((g * x * g⁻¹ : UA E n) : GA E n)) '' (D : Set (UA E n))
  have hK : IsCompact K := hD.image (continuous_subtype_val.comp ((continuous_const.mul continuous_id).mul continuous_const))
  have hKG : IsCompact (K ∩ ((ratGL E n).range : Set (GA E n))) := hK.inter_right hcl
  let t : Set (ratGL E n).range := {x | (x : GA E n) ∈ K}
  have himg : Subtype.val '' t = K ∩ ((ratGL E n).range : Set (GA E n)) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
    · rintro ⟨hy, hy'⟩; exact ⟨⟨y, hy'⟩, hy, rfl⟩
  have ht : IsCompact t := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]; exact hKG
  have hfin : (K ∩ ((ratGL E n).range : Set (GA E n))).Finite := by
    rw [← himg]; exact (ht.finite_of_discrete).image _
  by_contra hno
  have hinj := (injective_pow_iff_not_isOfFinOrder).2 hno
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((g * c ^ k * g⁻¹ : UA E n) : GA E n)) ?_ ?_ hfin
  · intro i j hij
    apply hinj
    have h1 : g * c ^ i * g⁻¹ = g * c ^ j * g⁻¹ := Subtype.ext hij
    simpa using h1
  · intro k
    refine ⟨⟨c ^ k, D.pow_mem hc k, rfl⟩, ?_⟩
    have hk : g * c ^ k * g⁻¹ ∈ ratU E n := by
      have := (ratU E n).pow_mem hgc k
      simpa [conj_pow] using this
    exact (Subgroup.mem_subgroupOf).1 hk

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaTauOrthonormalBasisSumCoordinates
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem map_inv_field_hom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  have h1 : A.adjugate.map f = (A.map f).adjugate := by
    have := RingHom.map_adjugate f A; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (A.map f).det = f A.det := by
    have := RingHom.map_det f A; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv', Ring.inverse_eq_inv', map_inv₀]

theorem lamB_sum_gK : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ (k : D.what₂.Tau × Fin N' × Fin N) (z : Bool × HH D) (a : Fin N) (b₀ : Fin N'), ∑ i, Formalism.L2.KerInert.RepFrame.lamB D lam b k i * ((gK D lam P P' b z a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p]) = chgB D lam P P' k ((0 : ZMod 1), (tauPl D z, a, b₀)) := by
  intro D p _ lam σ hσ hcl N N' L L' P P' _ _ r b hb k z a b₀
  obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl z
  set τ := tauPl D z with hτ
  let ι : MaximalUnramifiedExtension p →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype
  have hfun : ∀ y, ι (ρ y) = tauEmb D lam τ y := fun y => (hρ y).2
  have hrho : rhoK D lam z = fun y => ρ y := funext fun y => (hρ y).1
  have hinv : ∀ a a₁, ((((P τ).map (rhoK D lam z))⁻¹ a a₁ : MaximalUnramifiedExtension p) : ℂ_[p]) =
      ((P τ).map (tauEmb D lam τ))⁻¹ a a₁ := by
    intro a a₁
    have e2 : (P τ).map (tauEmb D lam τ) = ((P τ).map ρ).map ι := by
      ext u v; simp [hfun]
    rw [hrho, e2, ← map_inv_field_hom ι]; rfl
  have hg : ∀ i, ((gK D lam P P' b z a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p]) = ∑ b₁ : Fin N', ∑ a₁ : Fin N,
      Formalism.L2.KerInert.RepFrame.lamBc D lam b (τ, b₁, a₁) i *
        (tauEmb D lam τ (P' τ b₁ b₀) * ((P τ).map (tauEmb D lam τ))⁻¹ a a₁) := by
    intro i
    rw [gK, ← hτ]
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, coe_rhoK D lam σ hσ hcl, hinv, mul_assoc, ← hτ]
    rfl
  simp_rw [hg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b₁ _ => Finset.sum_comm).trans ?_
  simp_rw [← mul_assoc, ← Finset.sum_mul, hb k]
  rcases k with ⟨t, c, d⟩
  by_cases ht : t = τ
  · subst ht
    simp [chgB, Prod.ext_iff, ite_and]
  · simp [chgB, Prod.ext_iff, ht, Ne.symm ht]

end GlobalTheory.KerStd.HypCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearFormsHyperbolicCoordinatesEqTarget
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem sum_coef_fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hdual : ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0)
    (r₀ : R) (a : Fin N) (b : Fin N') (i : Fin r) (s : ZMod (nP D p)) :
    ∑ k, (if s.val % 2 = 0 then fOf D p σ om R g ((r₀, k), a, b) i * σ^[s.val] (oms k)
      else fOf' D p σ oms R g ((r₀, k), a, b) i * σ^[s.val] (om k)) = g (OrbitPlaces.orbMap D p r₀ s) a b i := by
  by_cases hs : s.val % 2 = 0
  · simp only [hs, if_true, fOf, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_eq_single s]
    · simp only [hs, if_true]
      have h := hdual s s rfl
      rw [if_pos rfl] at h
      calc ∑ k, σ^[s.val] (om k) * g (OrbitPlaces.orbMap D p r₀ s) a b i * σ^[s.val] (oms k)
          = g (OrbitPlaces.orbMap D p r₀ s) a b i * ∑ k, σ^[s.val] (om k) * σ^[s.val] (oms k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [h, mul_one]
    · intro t _ hts
      by_cases ht : t.val % 2 = 0
      · simp only [ht, if_true]
        have h := hdual t s (by rw [ht, hs])
        rw [if_neg hts] at h
        calc ∑ k, σ^[t.val] (om k) * g (OrbitPlaces.orbMap D p r₀ t) a b i * σ^[s.val] (oms k)
            = g (OrbitPlaces.orbMap D p r₀ t) a b i * ∑ k, σ^[t.val] (om k) * σ^[s.val] (oms k) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          _ = 0 := by rw [h, mul_zero]
      · simp [ht]
    · intro h; exact absurd (Finset.mem_univ s) h
  · simp only [hs, if_false, fOf', Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_eq_single s]
    · simp only [hs, if_false]
      have h := hdual s s rfl
      rw [if_pos rfl] at h
      calc ∑ k, σ^[s.val] (oms k) * g (OrbitPlaces.orbMap D p r₀ s) a b i * σ^[s.val] (om k)
          = g (OrbitPlaces.orbMap D p r₀ s) a b i * ∑ k, σ^[s.val] (om k) * σ^[s.val] (oms k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [h, mul_one]
    · intro t _ hts
      by_cases ht : t.val % 2 = 0
      · simp [ht]
      · simp only [ht, if_false]
        have h := hdual s t (by omega)
        rw [if_neg (Ne.symm hts)] at h
        calc ∑ k, σ^[t.val] (oms k) * g (OrbitPlaces.orbMap D p r₀ t) a b i * σ^[s.val] (om k)
            = g (OrbitPlaces.orbMap D p r₀ t) a b i * ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          _ = 0 := by rw [h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h

theorem hypZ_term (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {n : Type} (f f' : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension p) (i : n)
    (e : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1) :
    MvPowerSeries.C (f e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
      MvPowerSeries.C (f' e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2 =
    ∑ s : ZMod (nP D p), MvPowerSeries.C (((if s.val % 2 = 0 then f e i * σ^[s.val] (oms e.1.2)
      else f' e i * σ^[s.val] (om e.1.2) : MaximalUnramifiedExtension p)) : ℂ_[p]) * MvPowerSeries.X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) := by
  unfold linEv linOd
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s.val % 2 = 0
  · simp [hs, map_mul, mul_assoc]
  · simp [hs, map_mul, mul_assoc]

theorem bijective_orbMap (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hR : OrbitPlaces.IsReps D p R) :
    Function.Bijective (fun y : R × ZMod (nP D p) => OrbitPlaces.orbMap D p y.1 y.2) := by
  constructor
  · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ h
    simp only at h
    have hr : (r₁ : OrbitPlaces.Pl D) = r₂ := by
      obtain ⟨r0, _, hu⟩ := hR (OrbitPlaces.orbMap D p r₁ s₁)
      have e1 := hu r₁ ⟨r₁.2, s₁.val, rfl⟩
      have e2 := hu r₂ ⟨r₂.2, s₂.val, h.symm⟩
      rw [e1, e2]
    have hr' : r₁ = r₂ := Subtype.ext hr
    subst hr'
    have hs : s₁ = s₂ := ZMod.val_injective _ (posPl_inj D p r₁ _ _ (ZMod.val_lt s₁) (ZMod.val_lt s₂) h)
    rw [hs]
  · intro z
    obtain ⟨r0, ⟨hr0, e, he⟩, _⟩ := hR z
    refine ⟨(⟨r0, hr0⟩, (e : ZMod (nP D p))), ?_⟩
    show posPl D p r0 (e : ZMod (nP D p)).val = z
    rw [ZMod.val_natCast, posPl_mod, he]

end GlobalTheory.KerStd.HypCoord

namespace GlobalTheory.KerStd.HypCoord

theorem hypZ_fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hR : OrbitPlaces.IsReps D p R)
    (hdual : ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) (i : Fin r) :
    hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i =
      ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C ((g j.1 j.2.1 j.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X j := by
  set F : (R × Fin (nP D p / 2)) × Fin N × Fin N' → ZMod (nP D p) → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    fun e s => MvPowerSeries.C (((if s.val % 2 = 0 then fOf D p σ om R g e i * σ^[s.val] (oms e.1.2)
      else fOf' D p σ oms R g e i * σ^[s.val] (om e.1.2) : MaximalUnramifiedExtension p)) : ℂ_[p]) *
        MvPowerSeries.X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) with hF
  have hB : Function.Bijective (fun y : (R × ZMod (nP D p)) × Fin N × Fin N' => ((OrbitPlaces.orbMap D p y.1.1 y.1.2, y.2) :
      OrbitPlaces.Pl D × Fin N × Fin N')) :=
    (bijective_orbMap D p R hR).prodMap Function.bijective_id
  let eqv : ((R × ZMod (nP D p)) × Fin N × Fin N') × Fin (nP D p / 2) ≃
      ((R × Fin (nP D p / 2)) × Fin N × Fin N') × ZMod (nP D p) :=
    { toFun := fun y => (((y.1.1.1, y.2), y.1.2), y.1.1.2)
      invFun := fun x => (((x.1.1.1, x.2), x.1.2), x.1.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold hypZ
  calc ∑ e, (MvPowerSeries.C (fOf D p σ om R g e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
        MvPowerSeries.C (fOf' D p σ oms R g e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2)
      = ∑ e, ∑ s, F e s := Finset.sum_congr rfl fun e _ => hypZ_term D p σ om oms R _ _ i e
    _ = ∑ x : ((R × Fin (nP D p / 2)) × Fin N × Fin N') × ZMod (nP D p), F x.1 x.2 := (Fintype.sum_prod_type' F).symm
    _ = ∑ y : ((R × ZMod (nP D p)) × Fin N × Fin N') × Fin (nP D p / 2), F ((y.1.1.1, y.2), y.1.2) y.1.1.2 :=
        (Fintype.sum_equiv eqv _ _ fun _ => rfl).symm
    _ = ∑ y : (R × ZMod (nP D p)) × Fin N × Fin N', ∑ k, F ((y.1.1, k), y.2) y.1.2 :=
        Fintype.sum_prod_type' (fun (y : (R × ZMod (nP D p)) × Fin N × Fin N') (k : Fin (nP D p / 2)) => F ((y.1.1, k), y.2) y.1.2)
    _ = ∑ y : (R × ZMod (nP D p)) × Fin N × Fin N',
          MvPowerSeries.C ((g (OrbitPlaces.orbMap D p y.1.1 y.1.2) y.2.1 y.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) *
            MvPowerSeries.X ((OrbitPlaces.orbMap D p y.1.1 y.1.2, y.2) : OrbitPlaces.Pl D × Fin N × Fin N') := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← sum_coef_fOf D p σ om oms R g hdual y.1.1 y.2.1 y.2.2 i y.1.2, hF]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [← Finset.sum_mul, ← map_sum]
        congr 2
        push_cast
        rfl
    _ = _ := hB.sum_comp (fun j : OrbitPlaces.Pl D × Fin N × Fin N' =>
          MvPowerSeries.C ((g j.1 j.2.1 j.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X j)

theorem linForm_hypZ : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (κ : Type) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p) (Λ : κ → Fin r → ℂ_[p]) (T : κ → OrbitPlaces.Pl D × Fin N × Fin N' → ℂ_[p]), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 → ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) → (∀ q z a b, ∑ i, Λ q i * ((g z a b i : MaximalUnramifiedExtension p) : ℂ_[p]) = T q (z, a, b)) → ∀ q, ∑ i, MvPowerSeries.C (Λ q i) * hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i = ∑ j, MvPowerSeries.C (T q j) * MvPowerSeries.X j := by
  intro D p _ σ om oms R N N' r κ g Λ T _ hR hdual hT q
  simp only [hypZ_fOf D p σ om oms R g hR hdual, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hT q j.1 j.2.1 j.2.2, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_assoc]

end GlobalTheory.KerStd.HypCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCharDetEqOneOfCongrOneModPow
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.AwayMat

theorem muAt_det_congr_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ) (P : rowSG Pr sel mu) (n : ℕ) (k : Sp X.E n ≃ₗ[X.E] Sp X.E n),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E n) l))) →
    muAt Ch sel mu cst i P ((LinearEquiv.det k : X.Eˣ) : X.E) = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 _hX _hPr _hsel hL i P n k hk
  have hD : 1 ≤ cst.D P := hL.cst_ok.D_pos P
  have hq : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
  set Z : Fin n → Fin n → X.E := fun a b => (qOf P.1 : X.E) ^ (cst.D P - 1) *
    (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single b (1 : X.E)) a - (Pi.single b (1 : X.E) : Sp X.E n) a)) with hZ
  set A : Fin n → Fin n → X.E := fun a b => (Pi.single b (1 : X.E) : Sp X.E n) a with hA
  have hZi : ∀ a b, IntAt P.1 (Z a b) := fun a b => (intAt_pow (intAt_nat _) _).mul (hk b a)
  have hAi : ∀ a b, IntAt P.1 (A a b) := fun a b => by
    simp only [hA, Pi.single_apply]
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have hpow : (qOf P.1 : X.E) * (qOf P.1 : X.E) ^ (cst.D P - 1) = (qOf P.1 : X.E) ^ cst.D P := by
    rw [← pow_succ']
    congr 1
    omega
  have hM : LinearMap.toMatrix (Pi.basisFun X.E (Fin n)) (Pi.basisFun X.E (Fin n)) k.toLinearMap =
      Matrix.of fun a b => A a b + (qOf P.1 : X.E) * Z a b := by
    ext a b
    rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, Matrix.of_apply, hZ, hA]
    simp only
    rw [← mul_assoc, hpow, mul_inv_cancel_left₀ (pow_ne_zero _ hq)]
    simp
  have hdet : ((LinearEquiv.det k : X.Eˣ) : X.E) = Matrix.det (Matrix.of fun a b => A a b + (qOf P.1 : X.E) * Z a b) := by
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix (Pi.basisFun X.E (Fin n)), hM]
  have hA1 : (Matrix.of fun a b => A a b) = 1 := by
    ext a b
    simp [hA, Pi.single_apply, Matrix.one_apply, eq_comm]
  have hred : redP P.1 ((LinearEquiv.det k : X.Eˣ) : X.E) = redP P.1 (1 : X.E) := by
    rw [hdet, LastSteps.redP_det_add_q hAi hZi, hA1, Matrix.det_one]
  have h1 : IsUnit (redP P.1 (1 : X.E)) := by
    rw [reduction_one₂]
    exact isUnit_one
  have hu : IsUnit (redP P.1 ((LinearEquiv.det k : X.Eˣ) : X.E)) := hred ▸ h1
  unfold muAt
  rw [LastSteps.locChar_unit _ _ hu, LastSteps.unitV_congr _ hred]
  unfold LocE.unitV
  rw [dite_eq_left h1, show h1.unit = 1 from Units.ext reduction_one₂, map_one, Units.val_one]

end GlobalTheory.AwayMat
end
end

