module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepCharacterInverseTypeAtLifts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

theorem chr_mul_prod_top_core {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι)
    (Λ : LevFam B.fields.E B.fields.K (B.R.N B.R.m) (B.primes X).vGs)
    (hΛ : ∀ w, Λ w = levDiag (Nat.sub_le _ 1) (rowTyG I.Ch (rPsymF I.Ch) w))
    (Θ : LevQFam B.fields.E B.fields.K (B.R.N B.R.m) (I.Q a))
    (hΘ : ∀ Q, Θ Q = levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
      (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q))
    (x : Λ.grp) (y : Θ.grp)
    (g g' : SBof I a → Sp B.fields.E (B.R.N B.R.m) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N B.R.m)) (z : SBof I a → B.fields.K)
    (H : ∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) B.R.m P (g P) (z P) ∧
      (g' P ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N B.R.m) P.1 ∧
        (∀ h : P.1 ∈ (B.primes X).vGs, ∀ v ∈ stdAt B.fields.E (B.R.N B.R.m) P.1,
          redV P.1 (g' P v) = ((x.1 ⟨P.1, h⟩)⁻¹).1.mulVec (redV P.1 v)) ∧
        ∀ h : P.1 ∈ I.Q a, g' P = ((y.1 ⟨P.1, h⟩)⁻¹).1) ∧
      CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) :
    (((Λ.chr x * Θ.chr y : B.fields.Kˣ) : B.fields.K)) * ∏ P, z P = 1 := by
  classical
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_left.2 fun P h1 h2 => Q_notMem_of_ok hOk a P h2 h1
  have e2 : ∏ P, z P = (∏ w : (B.primes X).vGs, z ⟨w.1, Finset.mem_union_left _ w.2⟩) *
      ∏ Q : I.Q a, z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ := by
    rw [← Fintype.prod_equiv (Equiv.Finset.union _ _ hd) _ _ (fun _ => rfl), Fintype.prod_sum_type]
    rfl
  rw [e2, LevFam.chr_apply, levQ_chr_apply, Units.val_mul, Units.coe_prod, Units.coe_prod]
  have hG : ∀ w : (B.primes X).vGs, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨w.1, Finset.mem_union_left _ w.2⟩ = 1 := by
    intro w
    obtain ⟨⟨g'', hg''m, hpr, -, hz⟩, ⟨hg'G, hred, -⟩, hc⟩ := H ⟨w.1, Finset.mem_union_left _ w.2⟩
    have key : ∀ (l : Lev (𝓞 B.fields.E ⧸ w.1.asIdeal) B.fields.K (B.R.N B.R.m)),
        l = levDiag (Nat.sub_le _ 1) (rowTyG I.Ch (rPsymF I.Ch) w) → ∀ A (hA : A ∈ l.H),
        ∃ h0, ∃ hh0 : h0 ∈ (rowTyG I.Ch (rPsymF I.Ch) w).H, A = diagEmb _ (Nat.sub_le (B.R.N B.R.m) 1) h0 ∧
          l.lam ⟨A, hA⟩ = (rowTyG I.Ch (rPsymF I.Ch) w).lam ⟨h0, hh0⟩ := by
      intro l hl A hA
      subst hl
      obtain ⟨h0, hh0, rfl⟩ := hA
      exact ⟨h0, hh0, rfl, levDiag_lam _ _ rfl _ hh0⟩
    obtain ⟨h0, hh0, eA, elam⟩ := key _ (hΛ w) _ (x.2 w (Set.mem_univ w))
    rw [elam]
    have hmem : g'' ∈ LocE.JGsym w.1 (qOf w.1) B.R.k B.R.rS B.R.r B.R.t (B.R.N B.R.m - 1) 0 := by
      have h1 := hg''m
      unfold GlobalTheory.TwU.rowLevTop at h1
      rwa [if_pos w.2, hOk.sharp a, if_pos rfl] at h1
    have hz' : z ⟨w.1, Finset.mem_union_left _ w.2⟩ = LocE.lamGBS (qOf w.1) (psi0P I.Ch w.1) (chiP I.Ch w.1)
        B.R.k B.R.r B.R.t B.R.m (B.R.N B.R.m - 1) 0 g''.toLinearMap := by
      rw [hz]
      unfold GlobalTheory.TwU.rowChrTop
      rw [if_pos w.2, hOk.sharp a, if_pos rfl]
    have eA' : x.1 ⟨w.1, w.2⟩ = diagEmb _ (Nat.sub_le (B.R.N B.R.m) 1) h0 := eA
    have hred' : ∀ v ∈ stdAt B.fields.E (B.R.N B.R.m) w.1, redV w.1 (g' ⟨w.1, Finset.mem_union_left _ w.2⟩ v) =
        ((diagEmb (𝓞 B.fields.E ⧸ w.1.asIdeal) (Nat.sub_le (B.R.N B.R.m) 1) h0)⁻¹ : GL (Fin (B.R.N B.R.m)) _).1.mulVec (redV w.1 v) := by
      intro v hv
      rw [hred w.2 v hv, eA']
    have hc' : CongE w.1 1 (g ⟨w.1, Finset.mem_union_left _ w.2⟩) (g' ⟨w.1, Finset.mem_union_left _ w.2⟩) := by
      have h1 := hc
      unfold GlobalTheory.TwU.topDep at h1
      rwa [if_pos w.2] at h1
    rw [mul_comm, hz']
    exact _root_.GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one I.Ch w h0 hh0 _ _ g'' hmem hpr hg'G hred' hc'
  have hQ : ∀ Q : I.Q a, (((Θ Q).lam ⟨y.1 Q, y.2 Q (Set.mem_univ Q)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ = 1 := by
    intro Q
    obtain ⟨⟨g'', hg''m, hpr, -, hz⟩, ⟨-, -, hgy⟩, hc⟩ := H ⟨Q.1, Finset.mem_union_right _ Q.2⟩
    have hnot : Q.1 ∉ (B.primes X).vGs := Q_notMem_of_ok hOk a Q.1 Q.2
    have key : ∀ (l : LevI B.fields.E B.fields.K (B.R.N B.R.m) Q.1),
        l = levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M) (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q) →
        ∀ k (hk : k ∈ l.H), ∃ hk' : k ∈ (levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
          (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q)).H,
          l.lam ⟨k, hk⟩ = (levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
            (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q)).lam ⟨k, hk'⟩ := by
      intro l hl k hk
      subst hl
      exact ⟨hk, rfl⟩
    obtain ⟨hk', elam⟩ := key _ (hΘ Q) _ (y.2 Q (Set.mem_univ Q))
    rw [elam]
    have hmem : g'' ∈ LocE.JQ Q.1 (qOf Q.1) B.R.r (B.R.N B.R.m - 1) 0 := by
      have h1 := hg''m
      unfold GlobalTheory.TwU.rowLevTop at h1
      rwa [if_neg hnot] at h1
    have hz' : z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ = LocE.lamQB (resChar (I.tup a : Chr B.fields.F B.fields.E B.fields.K) Q.1)
        B.R.r (B.R.N B.R.m - 1) g''.toLinearMap := by
      rw [hz]
      unfold GlobalTheory.TwU.rowChrTop
      rw [if_neg hnot]
    have hc' : CongE Q.1 (2 * (I.cst a).M) (g ⟨Q.1, Finset.mem_union_right _ Q.2⟩) ((y.1 Q)⁻¹).1 := by
      have h1 := hc
      unfold GlobalTheory.TwU.topDep at h1
      rw [if_neg hnot, hgy Q.2] at h1
      exact h1
    rw [mul_comm, hz']
    exact _root_.GlobalTheory.TopRowsQ.lamQB_mul_levCong (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q _ _ (hOk.idx_ok a).cst_ok.M_pos (y.1 Q) hk' _ g'' hmem hpr hc'
  calc _ = (∏ w : (B.primes X).vGs, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : B.fields.Kˣ) : B.fields.K) *
        z ⟨w.1, Finset.mem_union_left _ w.2⟩) * ∏ Q : I.Q a, (((Θ Q).lam ⟨y.1 Q, y.2 Q (Set.mem_univ Q)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
    _ = 1 := by
        rw [Finset.prod_eq_one fun w _ => hG w, Finset.prod_eq_one fun Q _ => hQ Q, one_mul]

theorem chr_mul_prod_topVal : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m → ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  intro B X I hOk u a i hi b κ g g' z H
  subst hi
  rcases b with ⟨_ | b1, hb⟩
  swap
  · exact absurd (hb.1 rfl) (lt_irrefl _)
  exact chr_mul_prod_top_core I hOk a _ (fun w => congrFun (topLevAt_levG_m I.Ch I.sel (I.tup a) I.Ps _) w) _
    (fun Q => congrFun (topLevAt_levQ_m I.Ch I.sel (I.tup a) I.Ps _) Q) κ.2.1 κ.2.2 g g' z H

end GlobalTheory.Mem.Col2.AdT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelMapExtension
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtId

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def cmpConst (D : D7) (ka : ℂ) (δ : ℤˣ) (d : ℕ) : ℂ :=
  ka * (((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d)



theorem cmpConst_ne_zero {ka : ℂ} (hka : ka ≠ 0) (δ : ℤˣ) (d : ℕ) : cmpConst D ka δ d ≠ 0 := by
  have h1 : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have h2 : ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne'
  have h3 : ((δ : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 δ.ne_zero
  exact mul_ne_zero hka (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ (by norm_num))) (pow_ne_zero _ (inv_ne_zero h2)))


omit [Algebra T.Q.c.F D.what₂.LL] in
theorem ccIs_transport {θ : InfFam D} {V W : HSp D} {hr : W.rank = D.R.r} {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ')
    (hV : T.V j σ = W) (hV' : T.V j σ' = W) {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ}
    {cst : (T.U j σ).Comp → ℂ}
    (h : CcIs θ V W hr (T.U j σ) (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.x₀ j σ) om f₀ cst) :
    ∃ cst' : (T.U j σ').Comp → ℂ,
      CcIs θ V W hr (T.U j σ') (castDict hV' (T.dict j σ')) (castDict hV' (T.mu j σ')) (T.x₀ j σ') om f₀ cst' ∧
      ∀ g, cst' (castDict hV' (T.dict j σ') g).1 = cst (castDict hV (T.dict j σ) g).1 := by
  subst e
  exact ⟨cst, h, fun _ => rfl⟩


end GlobalTheory.PtId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LocSplice

theorem adAt_eq_of_prV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) {z z' : AfE F E}
    (h : Formalism.UG.prV (E := E) (P.under (𝓞 F)) z = Formalism.UG.prV (E := E) (P.under (𝓞 F)) z') :
    adAt F P z = adAt F P z' := by
  set v := P.under (𝓞 F)
  have h3 : adAt F P (Formalism.UG.P.afsplitEps E v) = 1 :=
    GlobalTheory.Mem.Col2.FullDt.adAt_eq_one_of_prV P (Formalism.UG.P.afsplit_prV_eps v)
  have e : ∀ w : AfE F E, adAt F P w =
      adAt F P (Formalism.UG.P.afsplitIE v (Formalism.UG.prV (E := E) v w)) := fun w => by
    rw [Formalism.UG.P.afsplit_decomp, map_mul, h3, one_mul]
  rw [e z, e z', h]

theorem map_conj_inv_mul {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (w w' A C : GL (Fin n) R)
    (h : ∀ r s, φ (w.1 r s) = φ (w'.1 r s)) (r s : Fin n) :
    φ ((((A⁻¹ * w * A)⁻¹ * C : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) r s) =
      φ ((((A⁻¹ * w' * A)⁻¹ * C : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) r s) := by
  have hΦ : Matrix.GeneralLinearGroup.map (n := Fin n) φ w = Matrix.GeneralLinearGroup.map φ w' := by
    apply Units.ext
    exact Matrix.ext h
  have h2 : Matrix.GeneralLinearGroup.map (n := Fin n) φ ((A⁻¹ * w * A)⁻¹ * C) =
      Matrix.GeneralLinearGroup.map φ ((A⁻¹ * w' * A)⁻¹ * C) := by
    simp only [map_mul, map_inv, hΦ]
  exact congrArg (fun z : GL (Fin n) S => (z : Matrix (Fin n) (Fin n) S) r s) h2

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ S.Uloc v → ∃ x ∈ S.U, ∀ (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep : SBof I a → ℕ) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P x g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g := by
  intro B X I hOk l Z a T i hi bad S P v hv κ hκ hloc
  refine ⟨Formalism.UG.P.afsplitU v (bc (prV (E := (I.rec7 l Z).host.E) v) κ) 1, ?_, ?_⟩
  · rw [S.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v _ _ _ _ (Formalism.UG.P.afsplit_bc_mem _ _ v κ hκ) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      rw [Formalism.UG.P.afsplit_right1]
      exact hloc
    · have h1 : bc (prV (E := (I.rec7 l Z).host.E) w) (Formalism.UG.P.afsplitU v (bc (prV (E := (I.rec7 l Z).host.E) v) κ) 1) = 1 := by
        apply Units.ext
        rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
        simp
      rw [h1]
      exact one_mem _
  · intro fb dep g hx
    have hseam := (_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a 0 0 P 1).1
    have hdict := fun z => (_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a ((I.rec7 l Z).R.N i) (dep P) P z).2.2
    have hvP : P.1.under (𝓞 B.host.F) = v := by
      apply HeightOneSpectrum.ext
      rw [hseam] at hv
      exact hv.symm
    unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hx ⊢
    have h1 := (hdict _).1 hx
    refine (hdict _).2 (fun r s => ?_)
    have h2 := h1 r s
    convert h2 using 3
    refine (map_conj_inv_mul _ _ _ _ _ (fun r s => ?_) r s).symm
    · apply adAt_eq_of_prV
      rw [hvP]
      exact congrFun (congrFun (Formalism.UG.P.afsplitC_prV (E := (I.rec7 l Z).host.E) v _ _) r) s

end GlobalTheory.Mem.Col2.AdT.LocSplice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZeroContentPlacesIffOverOfNonvanishing
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions

theorem mem_conjPl_iff {K : Type} [Field K] [StarRing K] (Q : HeightOneSpectrum (𝓞 K)) (y : 𝓞 K) :
    y ∈ (Formalism.DivisionValues.conjPl Q).asIdeal ↔ (Formalism.DivisionValues.cO K).symm y ∈ Q.asIdeal := by
  show y ∈ Ideal.map (Formalism.DivisionValues.cO K) Q.asIdeal ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, (Formalism.DivisionValues.cO K).apply_symm_apply y⟩

theorem coe_cO {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : ((Formalism.DivisionValues.cO K y : 𝓞 K) : K) = star (y : K) := rfl

theorem coe_cO_symm {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : (((Formalism.DivisionValues.cO K).symm y : 𝓞 K) : K) = star (y : K) := by
  have h := congrArg (fun u : 𝓞 K => (u : K)) ((Formalism.DivisionValues.cO K).apply_symm_apply y)
  simp only [coe_cO] at h
  rw [← h, star_star]

theorem over_conjPl {D D' : D7} {P : HeightOneSpectrum (𝓞 D.what₂.LL)} {P' : HeightOneSpectrum (𝓞 D'.what₂.LL)}
    (h : ∀ (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL), D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
      (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL)
    (hx : D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL)) :
    x ∈ (Formalism.DivisionValues.conjPl P).asIdeal ↔ x' ∈ (Formalism.DivisionValues.conjPl P').asIdeal := by
  rw [mem_conjPl_iff, mem_conjPl_iff]
  apply h
  rw [coe_cO_symm, coe_cO_symm, D.starLL_cx, D'.starLL_cx, hx]

theorem mem_zeroContentPlaces_iff_over_of_nonvanishing {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (hm : X.toD7.R.m = X'.toD7.R.m)
    (hN : ∀ (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m), (j : ℕ) = j' →
      ∀ (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL)),
        (∀ (x : 𝓞 X.toD7.what₂.LL) (x' : 𝓞 X'.toD7.what₂.LL),
          X.toD7.what₂.embLL (x : X.toD7.what₂.LL) = X'.toD7.what₂.embLL (x' : X'.toD7.what₂.LL) → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
        (NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P'))
    (v : X.B.places.Pl) (v' : X'.B.places.Pl) (hB : Below X.toD7 X'.toD7 v v') :
    v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 (fun _ _ => 0) := by
  have hB' := over_conjPl (D := X.toD7) (D' := X'.toD7) hB
  rw [Dat.mem_nonzero_index_places_iff_at_place_or_conjugate, Dat.mem_nonzero_index_places_iff_at_place_or_conjugate]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨⟨j, hm ▸ j.2⟩, ?_⟩
    exact hj.imp (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB).1 h) (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB').1 h)
  · rintro ⟨j', hj⟩
    refine ⟨⟨j', hm.symm ▸ j'.2⟩, ?_⟩
    exact hj.imp (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB).2 h) (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB').2 h)

theorem nzAt_iff_of {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m)
    (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL))
    (hI : (s0Of z.R z.F).Iw j (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 P ≠ 0 ↔
      (s0Of z'.R z'.F).Iw j' (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0 P' ≠ 0)
    (hJ : Formalism.DivisionValues.jw (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) P
          (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ↔
      Formalism.DivisionValues.jw (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).HT j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) P'
                (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) ≠ 0) :
    NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P' := by
  unfold NzAt
  exact or_congr hI (or_congr hJ Iff.rfl)

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeIdealTrivialAtChainBadPrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLatticeIdeal_trivial_at_chain_bad_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (I.J.amb B χ).AAUnit (Sall (Pr := B.primes X) I.sel (I.tup a) u) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.aaUnit_sall | exact GlobalTheory.Mem.Col2.AdT.aaUnit_sall | (intros; apply GlobalTheory.Mem.Col2.AdT.aaUnit_sall <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismCongruentNearFrameReading
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.NearCong

open WithZero

theorem mul_cong {K : Type} [Field K] (v : Valuation K ℤᵐ⁰) {n : ℕ} (N : ℕ) (A C : Matrix (Fin n) (Fin n) K)
    (hA : ∀ r s, v ((A - 1) r s) ≤ exp (-(N : ℤ))) (hC : ∀ r s, v ((C - 1) r s) ≤ exp (-(N : ℤ))) :
    ∀ r s, v ((A * C - 1) r s) ≤ exp (-(N : ℤ)) := by
  intro r s
  have he : exp (-(N : ℤ)) ≤ 1 := by
    rw [← exp_zero, exp_le_exp]; omega
  have e : A * C - 1 = (A - 1) * (C - 1) + (A - 1) + (C - 1) := by noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  refine v.map_add_le (v.map_add_le ?_ (hA r s)) (hC r s)
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun k _ => ?_
  rw [map_mul]
  calc v ((A - 1) r k) * v ((C - 1) k s) ≤ exp (-(N : ℤ)) * 1 := mul_le_mul' (hA r k) ((hC k s).trans he)
    _ = exp (-(N : ℤ)) := mul_one _

section Rat
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem congE_inv_mul (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (hC : CongE P c g' g) : ∀ x ∈ Formalism.L2.Col.stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x) ∈ Formalism.L2.Col.stdAt E n P := by
  intro x hx
  have hgi : g⁻¹ ∈ Formalism.L2.Col.GLint E n P := inv_mem hg
  have e1 : (g⁻¹ * g') x = g⁻¹ (g' x) := rfl
  have e2 : g⁻¹ (g x) = x := by
    show (g⁻¹ * g) x = x
    rw [inv_mul_cancel]; rfl
  have e : (((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x) = g⁻¹ ((((qOf P : ℕ) : E) ^ c)⁻¹ • (g' x - g x)) := by
    rw [map_smul, map_sub, e1, e2]
  rw [e]
  exact (hgi _).2 (hC x hx)

theorem val_entry (P : HeightOneSpectrum (𝓞 E)) (hq : P.valuation E ((qOf P : ℕ) : E) = exp (-1 : ℤ)) (c : ℕ)
    (h : Sp E n ≃ₗ[E] Sp E n)
    (hh : ∀ x ∈ Formalism.L2.Col.stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • (h x - x) ∈ Formalism.L2.Col.stdAt E n P) (r s : Fin n) :
    P.valuation E (LinearMap.toMatrix' h.toLinearMap r s - (1 : Matrix (Fin n) (Fin n) E) r s) ≤ exp (-(c : ℤ)) := by
  have hx : (Pi.single s (1 : E) : Sp E n) ∈ Formalism.L2.Col.stdAt E n P := by
    rw [GlobalTheory.TwistRowType.mem_stdAt]
    intro k
    rw [Pi.single_apply]
    split_ifs
    · exact (GlobalTheory.TwistRowType.intSub P).one_mem
    · exact (GlobalTheory.TwistRowType.intSub P).zero_mem
  have h1 := (GlobalTheory.TwistRowType.mem_stdAt P _).1 (hh _ hx) r
  rw [GlobalTheory.UnramCompletion.intAt_iff] at h1
  rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply, map_mul, map_inv₀, map_pow, hq] at h1
  have e : LinearMap.toMatrix' h.toLinearMap r s - (1 : Matrix (Fin n) (Fin n) E) r s = h (Pi.single s 1) r - (if r = s then 1 else 0) := by
    rw [LinearMap.toMatrix'_apply, Matrix.one_apply]; rfl
  rw [e]
  generalize P.valuation E (h (Pi.single s 1) r - if r = s then 1 else 0) = y at h1
  have hE : (exp (-1 : ℤ) ^ c)⁻¹ = exp (c : ℤ) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_neg]; congr 1; simp
  rw [hE] at h1
  have hm : exp (-(c : ℤ)) * exp (c : ℤ) = 1 := by rw [← exp_add]; simp
  calc y = (exp (-(c : ℤ)) * exp (c : ℤ)) * y := by rw [hm, one_mul]
    _ = exp (-(c : ℤ)) * (exp (c : ℤ) * y) := mul_assoc _ _ _
    _ ≤ exp (-(c : ℤ)) * 1 := mul_le_mul' le_rfl h1
    _ = exp (-(c : ℤ)) := mul_one _

end Rat

section Core
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem vAlg' (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

theorem adAt_ratA (P : HeightOneSpectrum (𝓞 E)) (γ : GL (Fin n) E) (r s : Fin n) :
    adAt F P (((GlobalTheory.TwU.ratA F γ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s) :=
  adAt_inclE F P _

theorem core (P : HeightOneSpectrum (𝓞 E)) (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = exp (-1 : ℤ))
    (hiff : ∀ (N : ℕ) (z : GL (Fin n) (AfE F E)), GlobalTheory.TwU.CongAt P N z ↔
      ∀ r s, Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ exp (-(N : ℤ)))
    (G : (Sp E n ≃ₗ[E] Sp E n) →* GL (Fin n) E)
    (hG : ∀ h r s, (G h : Matrix (Fin n) (Fin n) E) r s = LinearMap.toMatrix' h.toLinearMap r s)
    (c d : ℕ) (hcd : c ≤ d) (x : GL (Fin n) (AfE F E)) (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (h : GlobalTheory.TwU.CongAt P d (x⁻¹ * GlobalTheory.TwU.ratA F (G g))) (hC : CongE P c g' g) :
    GlobalTheory.TwU.CongAt P c (x⁻¹ * GlobalTheory.TwU.ratA F (G g')) := by
  have hq' : P.valuation E ((qOf P : ℕ) : E) = exp (-1 : ℤ) := by
    rw [← vAlg', map_natCast]
    exact hq
  have e : x⁻¹ * GlobalTheory.TwU.ratA F (G g') = (x⁻¹ * GlobalTheory.TwU.ratA F (G g)) * GlobalTheory.TwU.ratA F (G (g⁻¹ * g')) := by
    rw [mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [hiff] at h
  rw [hiff, e]
  have hdc : exp (-(d : ℤ)) ≤ exp (-(c : ℤ)) := by rw [exp_le_exp]; omega
  have key := mul_cong (Valued.v : Valuation (P.adicCompletion E) ℤᵐ⁰) c
    ((adAt F P).mapMatrix ((x⁻¹ * GlobalTheory.TwU.ratA F (G g) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)))
    ((adAt F P).mapMatrix ((GlobalTheory.TwU.ratA F (G (g⁻¹ * g')) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)))
    (fun r s => (h r s).trans hdc) (fun r s => ?_)
  · intro r s
    have := key r s
    rwa [← map_mul, ← Units.val_mul] at this
  · show Valued.v (adAt F P _ - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ _
    rw [adAt_ratA, hG]
    have h1 : (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s = algebraMap E _ ((1 : Matrix (Fin n) (Fin n) E) r s) := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [h1, ← map_sub, vAlg']
    exact val_entry P hq' c _ (congE_inv_mul P c g g' hg hC) r s

end Core

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → CongE P.1 (dep' P) g' g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' := by
  intro B X I hI l Z a i fb dep dep' P κ g g' hg hdep hIn hC
  unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hIn ⊢
  obtain ⟨hseam, hq, -⟩ := _root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a 0 0 P 1
  have hiff := fun N z => (_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a ((I.rec7 l Z).R.N i) N P z).2.2
  rw [hseam] at hIn hiff ⊢
  have i1 : NumberField ↥(I.rec7 l Z).host.F := inferInstance
  have i2 : NumberField (I.rec7 l Z).host.E := inferInstance
  exact @core (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ _ _ P.1 hq hiff (GlobalTheory.TwU.seamGL (sm I l Z)) (fun _ _ _ => rfl) (dep' P) (dep P) hdep _ g g' hg hIn hC

end GlobalTheory.Mem.Col2.AdT.NearCong
end
end

