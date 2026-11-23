module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSOmDecomp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSLocSB

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocalOfFam
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

def glueFam (K : Type) {F V : Type} [Field K] [Field F] [Algebra F K] [AddCommGroup V] [Module K V]
    (𝔭 : Ideal (𝓞 F)) {n m : ℕ} (b : Fin n → V) (a : Fin n → 𝓞 F) (π : 𝓞 F) (w : Fin m → V)
    (τ : Fin n → Fin m) : Fin n ⊕ Fin m → V :=
  Sum.elim (fun i => if vF 𝔭 (a i) = 0 then b i else
    ((algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i)) • (b i + w (τ i))) w

def FamTop : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) = ⊤

def FamGram : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      ∀ i j, h (glueFam K 𝔭 b a π w τ i) (glueFam K 𝔭 b a π w τ j) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)

def FamDual : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ)))) ≤
        locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ)))

def FamMeet : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ))) ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M

theorem glueAssemble_of (h0 : FamTop) (h1 : FamGram) (h2 : FamDual) (h3 : FamMeet) :
    GlueAssemble := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  refine ⟨locF 𝔭 (Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ))),
    ⟨_, (isLattice_span _ (h0 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg)).toIsLattice, rfl⟩,
    le_antisymm (h2 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg)
      (le_dualF_of_gram hF h h𝔭.isPrime _ (h1 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg)),
    h3 K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg⟩

theorem glueLocal_of_fam (hJ : JordanExists) (hV : GlueVecs) (h0 : FamTop) (h1 : FamGram)
    (h2 : FamDual) (h3 : FamMeet) : Formalism.L2.SG.Pf.G7.GlueLocal :=
  glueLocal_of_of hJ hV (glueAssemble_of h0 h1 h2 h3)

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcArith
section
noncomputable section

open Classical

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FieldDict {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  |(NumberField.discr X.B.I.F : ℝ)| = |(NumberField.discr D.host.F : ℝ)| ∧
  Fintype.card (NumberField.InfinitePlace X.B.I.F) = Module.finrank ℚ D.host.F ∧
  (∀ i : ℕ, 2 ≤ i → HasProd (fun v : PlX X =>
      (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i)⁻¹)
      (Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i)) ∧
  HasProd (fun v : PlX X => if (((D.mem u).A.T : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal then
      1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ D.R.k / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ D.R.k else 1)
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
      (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
        1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1)) ∧
  Formalism.HermitianLatticesTheory.vInv D.host.E = |(NumberField.discr D.host.F : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.F) / 2 ∧
  Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F ∧
  X.B.I.n = D.R.r ∧
  (∀ p : TypX X, absV p.1 (dV p.1) = 1) ∧
  (∀ p : TypX X, aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u') = aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u)) ∧
  ∏ p : TypX X, (gAt X p.1 : ℝ) = ((Lat.gS D : ℕ) : ℝ) ^ Module.finrank ℚ D.host.F

def NcArith : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (a' : ℝ),
    0 < a' → IsRowReps D F0 what₂ →
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' *
        ∏' v : PlX X,
          (omAt X.B.I.cm.sig X.B.I.J ψ v
            ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
            {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
              Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal →
    Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
              (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
              (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3) →
    IsCharAF X.B.I.F ψ → IsStdChar ψ → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    VolOrdV X u u' ψ → VolTypV X u u' ψ →
    (∀ p : TypX X,
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p /
          (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p =
        (gAt X p.1 : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) : ℕ) : ℤ)) /
          aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u)) →
    OmV X u' ψ → DiffProd X → Formalism.L2.SG.Pf.Cnt.RowsMass → FieldDict X u u' → ProdConv X u u' ψ →
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos →
    Formalism.L2.SG.Pf.NcAsm.NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq

end Formalism.L2.SG.Pf.NcVal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittAlg
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

section Form

variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

theorem hform_eq_dot (x y : Fin n → S) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_sub_left (x y z : Fin n → S) :
    hform s J (x - y) z = hform s J x z - hform s J y z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, ← sub_dotProduct]
  congr 1
  ext i
  simp

theorem hform_sub_right (x y z : Fin n → S) :
    hform s J x (y - z) = hform s J x y - hform s J x z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, mulVec_sub, dotProduct_sub]

theorem hform_add_left (x y z : Fin n → S) :
    hform s J (x + y) z = hform s J x z + hform s J y z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, ← add_dotProduct]
  congr 1
  ext i
  simp

theorem hform_add_right (x y z : Fin n → S) :
    hform s J x (y + z) = hform s J x y + hform s J x z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, mulVec_add, dotProduct_add]

theorem hform_smul_left (a : S) (x y : Fin n → S) :
    hform s J (a • x) y = s a * hform s J x y := by
  rw [hform_eq_dot, hform_eq_dot, ← smul_eq_mul, ← smul_dotProduct]
  congr 1
  ext i
  simp

theorem hform_smul_right (a : S) (x y : Fin n → S) :
    hform s J x (a • y) = a * hform s J x y := by
  rw [hform_eq_dot, hform_eq_dot, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hform_zero_left (y : Fin n → S) : hform s J 0 y = 0 := by simp [hform]

theorem hform_zero_right (x : Fin n → S) : hform s J x 0 = 0 := by simp [hform]

theorem hform_sum_right {ι : Type} (t : Finset ι) (c : ι → S) (v : ι → Fin n → S) (z : Fin n → S) :
    hform s J z (∑ i ∈ t, c i • v i) = ∑ i ∈ t, c i * hform s J z (v i) := by
  induction t using Finset.cons_induction with
  | empty => simp [hform_zero_right]
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, hform_add_right, hform_smul_right, ih]

theorem hform_sum_left {ι : Type} (t : Finset ι) (c : ι → S) (v : ι → Fin n → S) (z : Fin n → S) :
    hform s J (∑ i ∈ t, c i • v i) z = ∑ i ∈ t, s (c i) * hform s J (v i) z := by
  induction t using Finset.cons_induction with
  | empty => simp [hform_zero_left]
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, hform_add_left, hform_smul_left, ih]

theorem hform_conj (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (x y : Fin n → S) :
    s (hform s J x y) = hform s J y x := by
  have hJ' : ∀ i j, s (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [cT] using this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hs, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_single (i j : Fin n) :
    hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite]

theorem hform_entry (T : Matrix (Fin n) (Fin n) S) (i j : Fin n) :
    (cT s T * J * T) i j = hform s J (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1) := by
  rw [mulVec_single_one, mulVec_single_one]
  simp only [hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem unitary_of (T : Matrix (Fin n) (Fin n) S) (h : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w) :
    cT s T * J * T = J := by
  ext i j
  rw [hform_entry, h, hform_single]

def rT (u : Fin n → S) (ci lam : S) : Matrix (Fin n) (Fin n) S :=
  s lam • (1 - ci • vecMulVec u (vecMul (fun i => s (u i)) J))

theorem rT_mulVec (u : Fin n → S) (ci lam : S) (z : Fin n → S) :
    rT s J u ci lam *ᵥ z = s lam • (z - (ci * hform s J u z) • u) := by
  rw [rT, smul_mulVec, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
    ← hform_eq_dot, op_smul_eq_smul, smul_smul]

theorem rT_preserves (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (u : Fin n → S) (c ci lam : S)
    (hlam : lam * s lam = 1) (huu : hform s J u u = c + s c) (e2 : ci * c = 1) (z w : Fin n → S) :
    hform s J (rT s J u ci lam *ᵥ z) (rT s J u ci lam *ᵥ w) = hform s J z w := by
  have e3 : s ci * s c = 1 := by rw [← map_mul, e2, map_one]
  have hconj := hform_conj s J hs hJ
  rw [rT_mulVec, rT_mulVec]
  simp only [hform_smul_left, hform_smul_right, hform_sub_left, hform_sub_right, map_mul, hs, hconj]
  rw [huu]
  linear_combination
    (hform s J z w - ci * hform s J u w * hform s J z u
      - s ci * hform s J z u * (hform s J u w - ci * hform s J u w * (c + s c))) * hlam
    + hform s J z u * hform s J u w * (s ci * e2 + ci * e3)

def pM {a : ℕ} (t : Finset (Fin a)) (y : Fin a → Fin n → S) (β' : Fin a → S) : Matrix (Fin n) (Fin n) S :=
  ∑ i ∈ t, β' i • vecMulVec (y i) (vecMul (fun k => s (y i k)) J)

theorem pM_mulVec {a : ℕ} (t : Finset (Fin a)) (y : Fin a → Fin n → S) (β' : Fin a → S) (z : Fin n → S) :
    pM s J t y β' *ᵥ z = ∑ i ∈ t, (β' i * hform s J (y i) z) • y i := by
  unfold pM
  induction t using Finset.cons_induction with
  | empty => simp
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, add_mulVec, ih, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
      ← hform_eq_dot, op_smul_eq_smul, smul_smul]

end Form

section Int

variable {S : Type} [CommRing S] (O : Subring S)

theorem mulVec_mem {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (hM : ∀ i j, M i j ∈ O) (z : Fin n → S)
    (hz : ∀ k, z k ∈ O) (k : Fin n) : (M *ᵥ z) k ∈ O := by
  simp only [mulVec, dotProduct]
  exact O.sum_mem fun j _ => O.mul_mem (hM k j) (hz j)

theorem mul_mem' {n : ℕ} (M N : Matrix (Fin n) (Fin n) S) (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O)
    (i j : Fin n) : (M * N) i j ∈ O := by
  rw [Matrix.mul_apply]
  exact O.sum_mem fun k _ => O.mul_mem (hM i k) (hN k j)

theorem one_mem' {n : ℕ} (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) S) i j ∈ O := by
  rw [Matrix.one_apply]
  split_ifs
  exacts [O.one_mem, O.zero_mem]

variable (s : S →+* S) (hsO : ∀ z ∈ O, s z ∈ O)
include hsO

theorem hform_mem {n : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (x y : Fin n → S)
    (hx : ∀ k, x k ∈ O) (hy : ∀ k, y k ∈ O) : hform s J x y ∈ O :=
  O.sum_mem fun i _ => O.sum_mem fun j _ => O.mul_mem (O.mul_mem (hsO _ (hx i)) (hJ i j)) (hy j)

theorem cT_mem {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (hM : ∀ i j, M i j ∈ O) (i j : Fin n) :
    cT s M i j ∈ O := by
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  exact hsO _ (hM j i)

theorem vmv_mem {n : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (u : Fin n → S)
    (hu : ∀ k, u k ∈ O) (i j : Fin n) : vecMulVec u (vecMul (fun k => s (u k)) J) i j ∈ O := by
  simp only [vecMulVec_apply, vecMul, dotProduct]
  exact O.mul_mem (hu i) (O.sum_mem fun k _ => O.mul_mem (hsO _ (hu k)) (hJ k j))

theorem rT_mem {n : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (u : Fin n → S)
    (hu : ∀ k, u k ∈ O) (ci lam : S) (hci : ci ∈ O) (hlam : lam ∈ O) (i j : Fin n) : rT s J u ci lam i j ∈ O := by
  simp only [rT, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  exact O.mul_mem (hsO _ hlam) (O.sub_mem (one_mem' O i j) (O.mul_mem hci (vmv_mem O s hsO J hJ u hu i j)))

theorem pM_mem {n a : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (t : Finset (Fin a))
    (y : Fin a → Fin n → S) (hy : ∀ i k, y i k ∈ O) (β' : Fin a → S) (hβ' : ∀ i, β' i ∈ O) (i j : Fin n) :
    pM s J t y β' i j ∈ O := by
  simp only [pM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact O.sum_mem fun k _ => O.mul_mem (hβ' k) (vmv_mem O s hsO J hJ (y k) (hy k) i j)

end Int

end Formalism.L2.SG.Pf.NcS.IntWittAlg
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittLam
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
open scoped TensorProduct

theorem norm_id {S : Type} [CommRing S] (B p q a b D Θ : S) (h : Θ ^ 2 = D) :
    (B - (p - q * Θ) * (a + b * Θ)) * (B - (p + q * Θ) * (a - b * Θ)) =
      (B - p * a + q * b * D) ^ 2 - D * (q * a - p * b) ^ 2 := by
  linear_combination (q * b * (2 * (B - p * a) + q * b * (Θ ^ 2 + D)) - (p * b - q * a) ^ 2) * h

theorem norm_one {S : Type} [CommRing S] (p q D Θ : S) (h : Θ ^ 2 = D) :
    (p + q * Θ) * (p - q * Θ) = p ^ 2 - D * q ^ 2 := by
  linear_combination (-q ^ 2) * h

theorem core_loc {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] (ι : R →+* S) (s : S →+* S)
    (O : Subring S) (hιO : ∀ r, ι r ∈ O) (Θ : S) (hΘO : Θ ∈ O) (D Bt P Q a b : R)
    (hΘ : Θ ^ 2 = ι D) (hsΘ : s Θ = -Θ) (hsι : ∀ r, s (ι r) = ι r) (hPQ : P ^ 2 - D * Q ^ 2 = 1)
    (Bi K i4 : R) (hB : Bt * Bi = 1) (hK : Q * D * K = 1) (h4 : (4 : R) * i4 = 1) :
    ∃ lam ∈ O, lam * s lam = 1 ∧ ∃ c' ∈ O, (ι Bt - s lam * (ι a + ι b * Θ)) * c' = 1 := by
  let pp : Fin 4 → R := ![1, -1, P, -P]
  let qq : Fin 4 → R := ![0, 0, Q, -Q]
  let f : Fin 4 → R := fun i => (Bt - pp i * a + qq i * b * D) ^ 2 - D * (qq i * a - pp i * b) ^ 2
  have ef0 : f 0 = (Bt - a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring
  have ef1 : f 1 = (Bt + a) ^ 2 - D * b ^ 2 := by simp [f, pp, qq] <;> ring
  have ef2 : f 2 = (Bt - P * a + Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring
  have ef3 : f 3 = (Bt + P * a - Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := by simp [f, pp, qq] <;> ring
  have hspanTop : Ideal.span (Set.range f) = ⊤ := by
    have mem : ∀ i, f i ∈ Ideal.span (Set.range f) := fun i => Ideal.subset_span ⟨i, rfl⟩
    have ha : a ∈ Ideal.span (Set.range f) := by
      have : a = i4 * Bi * (f 1 - f 0) := by
        rw [ef1, ef0]; linear_combination (-a) * h4 + (-4 * i4 * a) * hB
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (mem 1) (mem 0))
    have hm : P * a - Q * D * b ∈ Ideal.span (Set.range f) := by
      have : P * a - Q * D * b = i4 * Bi * (f 3 - f 2) := by
        rw [ef3, ef2]
        linear_combination (-(P * a - Q * D * b)) * h4 + (-4 * i4 * (P * a - Q * D * b)) * hB
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (mem 3) (mem 2))
    have hb : b ∈ Ideal.span (Set.range f) := by
      have : b = K * (P * a - (P * a - Q * D * b)) := by linear_combination (-b) * hK
      rw [this]; exact Ideal.mul_mem_left _ _ (sub_mem (Ideal.mul_mem_left _ _ ha) hm)
    have hN : a ^ 2 - D * b ^ 2 ∈ Ideal.span (Set.range f) := by
      have : a ^ 2 - D * b ^ 2 = a * a - (D * b) * b := by ring
      rw [this]; exact sub_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
    have hB2 : Bt ^ 2 ∈ Ideal.span (Set.range f) := by
      have : Bt ^ 2 = f 0 + (2 * Bt) * a - (a ^ 2 - D * b ^ 2) := by rw [ef0]; ring
      rw [this]; exact sub_mem (add_mem (mem 0) (Ideal.mul_mem_left _ _ ha)) hN
    rw [Ideal.eq_top_iff_one]
    have : (1 : R) = Bi ^ 2 * Bt ^ 2 := by linear_combination (-(Bt * Bi + 1)) * hB
    rw [this]; exact Ideal.mul_mem_left _ _ hB2
  have hnorm : ∀ i, pp i ^ 2 - D * qq i ^ 2 = 1 := by
    intro i; fin_cases i <;> simp [pp, qq] <;> linear_combination hPQ
  obtain ⟨i, hi⟩ : ∃ i, IsUnit (f i) := by
    by_contra H
    push Not at H
    have hle : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal R := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).2 (H i)
    rw [hspanTop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 hle)
  set L : S := ι (pp i) + ι (qq i) * Θ with hL
  set M : S := ι (pp i) - ι (qq i) * Θ with hM
  have hsL : s L = M := by rw [hL, hM, map_add (f := _), map_mul, hsι, hsι, hsΘ]; ring
  have hsM : s M = L := by rw [hL, hM, map_sub, map_mul, hsι, hsι, hsΘ]; ring
  have hLM : L * M = 1 := by
    rw [hL, hM, norm_one _ _ _ _ hΘ, ← map_pow, ← map_pow, ← map_mul, ← map_sub, hnorm i, map_one]
  set c : S := ι Bt - M * (ι a + ι b * Θ) with hc
  set sc : S := ι Bt - L * (ι a - ι b * Θ) with hsc
  have hcc : c * sc = ι (f i) := by
    rw [hc, hsc, hL, hM]
    simp only [f, map_sub, map_add (f := _), map_mul, map_pow]
    exact norm_id _ _ _ _ _ _ _ hΘ
  obtain ⟨u, hu⟩ := hi
  have hLO : L ∈ O := O.add_mem (hιO _) (O.mul_mem (hιO _) hΘO)
  have hMO : M ∈ O := O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)
  refine ⟨L, hLO, by rw [hsL]; exact hLM, sc * ι ((u⁻¹ : Rˣ) : R), ?_, ?_⟩
  · exact O.mul_mem (O.sub_mem (hιO _) (O.mul_mem hLO (O.sub_mem (hιO _) (O.mul_mem (hιO _) hΘO)))) (hιO _)
  · rw [hsL, ← hc, ← mul_assoc, hcc, ← hu, ← map_mul, Units.mul_inv, map_one]

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplitPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.SplitPf

open Formalism.L2.SG.Pf.NcS

theorem omega_finite_volume_of_witt (hW : LocSBPf.WittLocT) (hI : LocSBPf.IntWittAE) : SplitSk.OmFinVol := by

  have hLoc : FinVolSk.LocSB := LocSBPf.locSB_of hW hI
  exact FinVolSk.omFinVol_of KfOrbPf.finite_orbit_holds hLoc BoxVolPf.box_volume_holds

theorem omega_splitting_of_witt (hW : LocSBPf.WittLocT) (hI : LocSBPf.IntWittAE) : Formalism.L2.SG.Pf.NcSplitS.SplitOm := by

  apply SplitSk.splitOm_of AdTupPf.admissible_tuple_holds OmDecompPf.omega_decomposition_holds
  exact omega_finite_volume_of_witt hW hI

theorem splitOm_of_intWitt (hI : LocSBPf.IntWittAE) : Formalism.L2.SG.Pf.NcSplitS.SplitOm := by

  exact omega_splitting_of_witt WittLocPf.local_witt_theorem hI

end Formalism.L2.SG.Pf.NcS.SplitPf
end
end

