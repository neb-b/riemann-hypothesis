module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmulMemOfOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProof
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0304

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProof
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm.FibProof
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem spH_B (x y : S.V) : (spH S).B x y = S.hT y x := rfl

theorem frF_e (F : FlagG S r T) (hT : T ≠ 0) (a : Fin (r + 1)) : (frF F hT).e a = F.fvec a := rfl

theorem frF_Xa (F : FlagG S r T) (hT : T ≠ 0) (k : ℕ) : (frF F hT).Xa k = F.Xa k := by

  have h : (fun b : Fin r => (frF F hT).e b.castSucc) = F.e := by
    funext b
    simp [frF_e, FlagG.fvec]
  rw [Formalism.HermitianLatticeCounting.S6.FlagD.Xa, h, FlagG.Xa]

theorem frF_X (F : FlagG S r T) (hT : T ≠ 0) : (frF F hT).X = F.X := by
  rw [Formalism.HermitianLatticeCounting.S6.FlagD.X, frF_Xa, FlagG.Xa, FlagG.X]
  congr 1
  ext x
  simp

end Gen

section Bridge
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem isom_of_B {n : S.V ≃ₗ[E] S.V} (h : ∀ x y, (spH S).B (n x) (n y) = (spH S).B x y) :
    n ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  intro x y
  have h1 := h y x
  rw [spH_B, spH_B] at h1
  exact h1

theorem gmap_eq_smul (n : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) : Formalism.HermitianLatticesTheory.gmap n Λ = n • Λ := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_smul_pointwise_iff_exists, LinearEquiv.smul_def]

theorem nlam_of_inN (F : FlagG S r T) (hT : T ≠ 0) {n : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (h : (frF F hT).InN (n : S.V →ₗ[E] S.V)) (hΛ : n • Λ = Λ) : n ∈ NLam Λ (⟨F, F.z⟩ : LFlag S r T) := by
  obtain ⟨hB, -, he, hperp⟩ := h

  have hfe : ∀ b : Fin r, (frF F hT).e b.castSucc = F.e b := fun b => by
    simp [frF_e, FlagG.fvec]
  refine ⟨⟨isom_of_B hB, (gmap_eq_smul n Λ).trans hΛ⟩, ?_, ?_⟩
  ·
    intro j x hx
    have hle : F.Xa (j + 1) ≤ (F.Xa j).comap ((n : S.V →ₗ[E] S.V) - LinearMap.id) := by
      rw [FlagG.Xa, Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.val < j + 1 := hb
      have h3 := he b
      rw [hfe, frF_Xa] at h3
      have hmono : F.Xa b.val ≤ F.Xa j :=
        Submodule.span_mono (Set.image_mono fun i (hi : i.val < b.val) => show i.val < j by omega)
      exact hmono h3
    simpa using hle hx
  ·
    intro y hy
    have hy' : ∀ x ∈ F.X, S.hT x y = 0 := by
      intro x hx
      have := (Submodule.mem_iInf _).mp hy x
      simpa using (Submodule.mem_iInf _).mp this hx
    have h4 := hperp y (fun a => by
      rw [hfe]
      have h5 := (spH S).herm y (F.e a)
      rw [spH_B, hy' _ (Submodule.subset_span (Set.mem_range_self a)), star_zero] at h5
      exact h5.symm)
    rw [frF_X] at h4
    exact h4

end Bridge

def mapD {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
    (F : Formalism.HermitianLatticeCounting.S6.FlagD H r) (φ : V ≃ₗ[K] V) (hφ : ∀ x y, H.B (φ x) (φ y) = H.B x y) : Formalism.HermitianLatticeCounting.S6.FlagD H r where
  e a := φ (F.e a)
  T := F.T
  indep := F.indep.map' (φ : V →ₗ[K] V) (LinearEquiv.ker φ)
  iso a b := by rw [hφ]; exact F.iso a b
  zperp a := by rw [hφ]; exact F.zperp a
  zz := by rw [hφ]; exact F.zz
  hT := F.hT

section Obj
variable {D : D7} {X : HidaSetting D}

theorem Ft_e {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (a : Fin (D.R.rS + 1)) :
    (Ft t).e a = t.lin ((F0 X u).e a) := by
  have h : t.rep.1.2 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  change (frq X t.rep).fl.fvec a = t.rep.1.2 ((X.Fu u).fvec a)
  simp only [frq, mapLF, h, dite_true]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simp [FlagG.fvec, mapFlag]
  · simp [FlagG.fvec, mapFlag]

theorem Ft_Xa {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (k : ℕ) :
    (Ft t).Xa k = ((F0 X u).Xa k).map (t.lin : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  simp only [Formalism.HermitianLatticeCounting.S6.FlagD.Xa, Submodule.map_span, Set.image_image, Ft_e, LinearEquiv.coe_coe]

end Obj

theorem mem_line {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] {A : Submodule (𝓞 K) K} {v : V} {t : K} (ht : t ∈ A) :
    t • v ∈ GlobalTheory.DegCnt.line A v := by
  exact Submodule.mem_map.mpr ⟨t, ht, by simp⟩

section Main
variable {D : D7} {X : HidaSetting D}

theorem line_e_le (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (a : Fin D.R.rS) :
    GlobalTheory.DegCnt.line (N.aa a) (N.F.e a.castSucc) ≤ N.P0 := by
  unfold GlobalTheory.DegCnt.NF.P0
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_iSup (fun b => GlobalTheory.DegCnt.line (N.aa b) (N.F.e b.castSucc)) a)))

theorem line_z_le (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) : GlobalTheory.DegCnt.line 1 N.F.z ≤ N.P0 := by
  unfold GlobalTheory.DegCnt.NF.P0
  exact le_sup_of_le_left le_sup_right

theorem stab_of_fix (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : a ∈ stabF D (X.Fu u) := by
  have he : ∀ b, a ((X.Fu u).e b) = (X.Fu u).e b := fun b => by
    have h : a ((X.Fu u).fvec b.castSucc) = (X.Fu u).fvec b.castSucc := hfix b.castSucc
    simpa [FlagG.fvec] using h
  have hz : a (X.Fu u).z = (X.Fu u).z := by
    have h : a ((X.Fu u).fvec (Fin.last _)) = (X.Fu u).fvec (Fin.last _) := hfix (Fin.last _)
    simpa [FlagG.fvec] using h
  refine ⟨hi, fun j => ?_, hz⟩
  rw [FlagG.Xa, Submodule.map_span, Set.image_image]
  simp [he]

theorem gmap_one' (L : Submodule (𝓞 D.host.E) (VS D).V) : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
  rw [gmap_eq_smul, one_smul]

end Main

theorem fibC : FibC := by
  intro D large₂ X Y u hStd t₁ t₂ hlam hEq
  obtain ⟨n₀, hnN, hnΛ, hnG⟩ := hEq

  have hi₁ : t₁.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₁.rep.2.2.1
  have hi₂ : t₂.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₂.rep.2.2.1
  have hin : n₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := isom_of_B hnN.1
  have hg₁ : t₁.lin • t₁.lam' = t₂.lam := by
    rw [← gmap_eq_smul, ← hlam]
    exact t₁.rep.2.2.2.1
  have hg₂ : t₂.lin • t₂.lam' = t₂.lam := by
    rw [← gmap_eq_smul]
    exact t₂.rep.2.2.2.1
  have hnΛ' : n₀ • t₂.lam = t₂.lam := hlam ▸ hnΛ

  obtain ⟨g, hg⟩ : ∃ g : (VS D).V ≃ₗ[D.host.E] (VS D).V, g = t₂.lin⁻¹ * n₀ * t₁.lin := ⟨_, rfl⟩
  have hgi : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hg ▸ mul_mem (mul_mem (inv_mem hi₂) hin) hi₁
  have hgB : ∀ x y, (HV D).B (g x) (g y) = (HV D).B x y := fun x y => by
    rw [spH_B, spH_B]
    exact hgi y x
  have hgl : g • t₁.lam' = t₂.lam' := by
    rw [hg, mul_smul, mul_smul, hg₁, hnΛ', ← hg₂, inv_smul_smul]
  have hgmem : ∀ x ∈ t₁.lam', g x ∈ t₂.lam' := fun x hx => by
    have h := Submodule.smul_mem_pointwise_smul x g t₁.lam' hx
    rw [hgl] at h
    exact h

  let G : Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS := mapD (F0 X u) g hgB
  have hSG : GlobalTheory.DegAsm.SameGr (F0 X u) G := by
    intro a
    have h := hnG a
    rw [Ft_e, Ft_e, Ft_Xa, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply] at h
    show g ((F0 X u).e a) - (F0 X u).e a ∈ (F0 X u).Xa a.val
    rw [hg]
    exact h

  obtain ⟨N₁, hF₁, -, -, -, hd₁, -, hRef₁, -⟩ := _root_.GlobalTheory.IdNF.idNFC_holds D large₂ X Y u hStd t₁.lam' (Or.inl t₁.mem')
  obtain ⟨N₂, hF₂, -, -, -, hd₂, hTm₂, hRef₂, -⟩ := _root_.GlobalTheory.IdNF.idNFC_holds D large₂ X Y u hStd t₂.lam' (Or.inl t₂.mem')
  have hP₁ : N₁.P0 ≤ t₁.lam' :=
    (show N₁.P0 ≤ N₁.Ref (GlobalTheory.HermLat.latL N₁.F N₁.F' t₁.lam') from le_sup_left).trans hRef₁.le
  have hP₂ : N₂.P0 ≤ t₂.lam' :=
    (show N₂.P0 ≤ N₂.Ref (GlobalTheory.HermLat.latL N₂.F N₂.F' t₂.lam') from le_sup_left).trans hRef₂.le
  have haa : ∀ a, N₂.aa a = N₁.aa a := fun a => by
    simp only [GlobalTheory.DegCnt.NF.aa, hd₁, hd₂]
  have he₁ : ∀ a : Fin D.R.rS, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₁.lam' := by
    intro a s hs
    have h := hP₁ (line_e_le N₁ a (mem_line (v := N₁.F.e a.castSucc) ((haa a) ▸ hs)))
    rwa [hF₁] at h
  have he₂ : ∀ a : Fin D.R.rS, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₂.lam' := by
    intro a s hs
    have h := hP₂ (line_e_le N₂ a (mem_line (v := N₂.F.e a.castSucc) hs))
    rwa [hF₂] at h
  have hone : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hz₁ : (F0 X u).z ∈ t₁.lam' := by
    have h := hP₁ (line_z_le N₁ (mem_line (v := N₁.F.z) hone))
    rwa [one_smul, hF₁] at h
  have hz₂ : (F0 X u).z ∈ t₂.lam' := by
    have h := hP₂ (line_z_le N₂ (mem_line (v := N₂.F.z) hone))
    rwa [one_smul, hF₂] at h
  have hU₂ : GlobalTheory.HermLat.IsUnimod (HV D) t₂.lam' := hTm₂.1.1
  have hFr₂ : GlobalTheory.HermLat.IsFrame (F0 X u) t₂.lam' N₂.aa := hF₂ ▸ hTm₂.1.2.1
  have hint : ∀ a, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₂.lam' ∧ s • G.e a.castSucc ∈ t₂.lam' := by
    intro a s hs
    refine ⟨he₂ a s hs, ?_⟩
    have h := hgmem _ (he₁ a s hs)
    rw [map_smul] at h
    exact h
  have hGz : G.z ∈ t₂.lam' := hgmem _ hz₁

  have hK := (_root_.GlobalTheory.TypeAsm.hostC D large₂ hStd).1
  obtain ⟨m, hmN, hmΛ, hmE⟩ := GlobalTheory.DegAsm.FrameMove.main D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) G N₂.aa
    t₂.lam' hU₂ hFr₂ hSG rfl hint hz₂ hGz

  have hai : g⁻¹ * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hgi) (isom_of_B hmN.1)
  have hafix : ∀ b, (g⁻¹ * m) ((F0 X u).e b) = (F0 X u).e b := fun b => by
    show g.symm (m ((F0 X u).e b)) = (F0 X u).e b
    rw [hmE b]
    exact g.symm_apply_apply _
  have hamap : (g⁻¹ * m) • t₂.lam' = t₁.lam' := by
    rw [mul_smul, hmΛ, ← hgl, inv_smul_smul]

  have hrow := (Y.rowsOK u).2 t₁.lam' ((Y.rowsOK u).1 _ t₁.mem')
  have hl : t₂.lam' = t₁.lam' :=
    hrow.unique ⟨t₂.mem', g⁻¹ * m, stab_of_fix u hai hafix, (gmap_eq_smul _ _).trans hamap⟩
      ⟨t₁.mem', 1, stab_of_fix u (one_mem _) (fun _ => rfl), gmap_one' _⟩
  refine ⟨hl.symm, n₀, g⁻¹ * m, nlam_of_inN (X.Fu u) (tu_ne D u) hnN hnΛ, hai, ?_, hafix, m⁻¹, ?_, ?_⟩
  · rw [gmap_eq_smul]
    rw [hl] at hamap
    exact hamap
  · have hmΛ' : m • t₁.lam' = t₁.lam' := by
      rw [← hl]
      exact hmΛ
    exact GlobalTheory.LoopC.FrEqv.symm_mem_NLam (nlam_of_inN (X.Fu u) (tu_ne D u) hmN hmΛ')
  · rw [hg]
    group

end GlobalTheory.TypeAsm.FibProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicU.Cofinite

open Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_mem_intLoc_iff_repr {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] E, y ∈ intLoc F E v ↔
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F := by
  classical
  set ω := Module.Free.chooseBasis ℤ (𝓞 E) with hω
  have hI : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E), z ∈ intLoc F E v ↔
      z ∈ AddSubgroup.closure {z : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E,
        z = a ⊗ₜ[F] (x : E)} := fun _ _ => Iff.rfl
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ j k,
      algebraMap F (Fv F v) (b.repr ((ω j : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]
    intro j k
    exact eventually_algebraMap_mem_integers _
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ k,
      (1 : Fv F v) ⊗ₜ[F] b k ∈ intLoc F E v := by
    rw [Filter.eventually_all]
    intro k
    exact eventually_one_tmul_mem_intLoc _
  filter_upwards [h1, h2] with v h1 h2 y
  have key : ∀ (x : 𝓞 E) (k : Fin d),
      algebraMap F (Fv F v) (b.repr (x : E) k) ∈ v.adicCompletionIntegers F := by
    intro x k
    have hx : (x : E) = ∑ j, (ω.repr x j) • ((ω j : 𝓞 E) : E) := by
      have := congrArg (algebraMap (𝓞 E) E) (ω.sum_repr x)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simp only [map_zsmul] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact zsmul_mem (h1 j k) _
  constructor
  · intro hy
    rw [hI] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      intro k
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul]
      exact mul_mem ha (key x k)
    | zero => intro k; simp
    | add z w _ _ hz hw =>
      intro k
      rw [map_add (f := _), Finsupp.add_apply]
      exact add_mem (hz k) (hw k)
    | neg z _ hz =>
      intro k
      rw [map_neg, Finsupp.neg_apply]
      exact neg_mem (hz k)
  · intro hy
    rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
    refine sum_mem fun k _ => ?_
    rw [Algebra.TensorProduct.basis_apply, Algebra.smul_def]
    refine mul_mem ?_ (h2 k)
    rw [hI]
    refine AddSubgroup.subset_closure ⟨_, hy k, 1, ?_⟩
    simp [Algebra.TensorProduct.algebraMap_apply]

theorem eventually_latLoc_eq_latV :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
      (b : Module.Basis (Fin d) F E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L →
      ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} = latV b v := by
  intro F E _ _ _ _ _ n d b L hL
  have : Submodule.IsFullLattice E L := hL
  have : Submodule.IsFullLattice E (stdLattice E n) := isLattice_stdLattice
  filter_upwards [eventually_latLoc_eq F L (stdLattice E n), eventually_mem_intLoc_iff_repr b]
    with v hv h1
  have hI : ∀ z : Fv F v ⊗[F] E, z ∈ intLoc F E v ↔
      z ∈ AddSubgroup.closure {z : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E,
        z = a ⊗ₜ[F] (x : E)} := fun _ => Iff.rfl
  have hS : ∀ y : Fin n → Fv F v ⊗[F] E, y ∈ latLoc F (stdLattice E n) v ↔
      y ∈ AddSubgroup.closure {y : Fin n → Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F,
        ∃ x ∈ stdLattice E n, y = fun i => a ⊗ₜ[F] x i} := fun _ => Iff.rfl
  have hstd : ∀ x : Fin n → E, x ∈ stdLattice E n ↔ ∀ i, ∃ z : 𝓞 E, (z : E) = x i := by
    intro x
    unfold stdLattice Formalism.UG.stdLat
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range,
      Algebra.linearMap_apply]
  have hloc : ∀ y, y ∈ latLoc F (stdLattice E n) v ↔ ∀ i, y i ∈ intLoc F E v := by
    intro y
    constructor
    · intro hy i
      rw [hS] at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        obtain ⟨w, hw⟩ := (hstd x).1 hx i
        rw [hI]
        exact AddSubgroup.subset_closure ⟨a, ha, w, by rw [hw]⟩
      | zero => exact zero_mem _
      | add z w _ _ hz hw => exact add_mem hz hw
      | neg z _ hz => exact neg_mem hz
    · intro hy
      rw [← Finset.univ_sum_single y, hS]
      refine sum_mem fun i _ => ?_
      have hyi := hy i
      rw [hI] at hyi
      revert hyi
      generalize y i = z0
      intro hyi
      induction hyi using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : E), (hstd _).2 fun j => ?_, ?_⟩
        · by_cases h : j = i
          · subst h
            exact ⟨x, by simp⟩
          · exact ⟨0, by simp [h]⟩
        · funext j
          by_cases h : j = i
          · subst h
            simp
          · simp [h]
      | zero => simp
      | add z w _ _ hz hw =>
        rw [Pi.single_add]
        exact add_mem hz hw
      | neg z _ hz =>
        rw [Pi.single_neg]
        exact neg_mem hz
  ext X
  unfold latV
  simp only [Set.mem_ofPred_eq, hv, hloc, h1, Fin.forall_fin_one]

end GlobalTheory.AdelicU.Cofinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsDerLowKSub
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.DerEx


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothOnG_comb {n : ℕ} {ε : Fin n → Bool} {f g : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hg : SmoothOnG ε g) : SmoothOnG ε (fun x => c * f x + g x) := by
  intro x hx
  obtain ⟨U, F, hU, hxU, hF, hFf⟩ := hf x hx
  obtain ⟨U', G, hU', hxU', hG, hGg⟩ := hg x hx
  refine ⟨U ∩ U', fun y => c * F y + G y, hU.inter hU', ⟨hxU, hxU'⟩,
    (contDiffOn_const.mul (hF.mono Set.inter_subset_left)).add (hG.mono Set.inter_subset_right), ?_⟩
  intro y hy hyJ
  simp only [hFf y hy.1 hyJ, hGg y hy.2 hyJ]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothOnG_zero {n : ℕ} (ε : Fin n → Bool) : SmoothOnG ε (fun _ => 0) := fun _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem exists_isDer_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsDer ε σ V E ∧ lowKSub ε lam σ ≤ V := by
  intro n ε lam H _ _ _ σ hσ hK
  let S : Set H := {v | ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), SmoothOnG ε α ∧
    HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
    ∀ y : H, ∫ g : UJ ε, α (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v⟫_ℂ}
  have hder : ∀ v ∈ Submodule.span ℂ S, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X →
      ∃ v' ∈ Submodule.span ℂ S,
        HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0 := by
    intro v hv X hX
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      obtain ⟨β, v', k1, k2, k3, k4⟩ :=
        (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).2 X hX
      exact ⟨v', Submodule.subset_span ⟨β, s, k1, k2, k3⟩, k4⟩
    | zero => exact ⟨0, zero_mem _, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', hda⟩ := ha
      obtain ⟨b', hb', hdb⟩ := hb
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      simp only [map_add (f := _)]
      exact hda.add hdb
    | smul c a _ ha =>
      obtain ⟨a', ha', hda⟩ := ha
      refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
      simp only [map_smul]
      exact hda.const_smul c
  have hzero := smoothOnG_zero ε
  have hsm : ∀ v ∈ Submodule.span ℂ S, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ) := by
    intro v hv y
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      exact (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).1 y
    | zero => simpa using hzero
    | add a b _ _ ha hb => simpa [inner_add_right] using smoothOnG_comb 1 ha hb
    | smul c a _ ha => simpa [inner_smul_right] using smoothOnG_comb c ha hzero
  obtain ⟨E, hE⟩ := GlobalTheory.DerOf.exists_isDer n ε H σ (Submodule.span ℂ S) hσ hder hsm
  obtain ⟨α, h1, h2, h3⟩ := GlobalTheory.exists_smooth_fix_lowKSub n ε lam H σ hσ hK
  exact ⟨_, E, hE, fun s hs => Submodule.subset_span ⟨α, s, h1, h2, h3 s hs⟩⟩

end GlobalTheory.DerEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicLatticeClosureIffSwapMemSpanStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicLatticeClosure_iff_swap_mem_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → Af F ⊗[F] E), y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔ (fun i => Algebra.TensorProduct.comm F (Af F) E (y i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  first | exact @GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf | exact GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf | (intros; apply GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf <;> assumption)
end

