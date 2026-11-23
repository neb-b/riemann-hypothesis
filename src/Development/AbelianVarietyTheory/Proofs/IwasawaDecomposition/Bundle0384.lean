module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0373
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Bundle0026
public import Formalism.LocalToGlobal.Columns.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Formalism.LocalToGlobal.Columns.RecLevelLocK
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0376
public import Formalism.LocalToGlobal.Columns.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBasisFreeModulePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem charpoly_eq_prod_of_iSup_eigenspace {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (s : Finset K)
    (h : ⨆ r ∈ s, f.eigenspace r = ⊤) :
    ∃ m : Multiset K, f.charpoly = (m.map fun a => X - C a).prod := by
  classical
  let E : s → Submodule K V := fun r => f.eigenspace (r : K)
  have hind : iSupIndep E := (Module.End.eigenspaces_iSupIndep f).comp Subtype.val_injective
  have htop : iSup E = ⊤ := by
    rw [← h, iSup_subtype]
  have hint : DirectSum.IsInternal E :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top E).mpr ⟨hind, htop⟩
  let bE : ∀ r : s, Module.Basis (Module.Free.ChooseBasisIndex K (E r)) K (E r) :=
    fun r => Module.Free.chooseBasis K (E r)
  let bb := hint.collectedBasis bE
  have hdiag : LinearMap.toMatrix bb bb f = Matrix.diagonal (fun x => ((x.1 : s) : K)) := by
    ext x y
    rw [LinearMap.toMatrix_apply]
    have hy : (bb y : V) = (bE y.1 y.2 : V) := by
      rw [hint.collectedBasis_coe]
    have hev : f (bE y.1 y.2 : V) = ((y.1 : s) : K) • (bE y.1 y.2 : V) :=
      Module.End.mem_eigenspace_iff.mp (bE y.1 y.2).2
    rw [hy, hev, ← hy, map_smul, bb.repr_self, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hxy), if_neg hxy, smul_zero]
  refine ⟨Finset.univ.val.map (fun x : (Σ r : s, Module.Free.ChooseBasisIndex K (E r)) => ((x.1 : s) : K)), ?_⟩
  rw [← LinearMap.charpoly_toMatrix f bb, hdiag, Matrix.charpoly_diagonal, Multiset.map_map,
    Finset.prod_eq_multiset_prod]
  rfl

theorem charpoly_restrict_map_eq_prod {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V]
    [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
    (B : Submodule O V) [Module.Free O B] [Module.Finite O B] (f : Module.End (FractionRing O) V)
    (hf : ∀ x ∈ B, f x ∈ B) (s : Finset (FractionRing O))
    (hs : ∀ x ∈ B, x ∈ ⨆ r ∈ s, f.eigenspace r) :
    ∃ m : Multiset (FractionRing O), (LinearMap.charpoly ((f.restrictScalars O).restrict hf)).map
      (algebraMap O (FractionRing O)) = (m.map fun a => X - C a).prod := by
  classical
  let b := Module.Free.chooseBasis O B
  let v : Module.Free.ChooseBasisIndex O B → V := fun i => (b i : V)
  have hliO : LinearIndependent O v := b.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  have hli : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hliO
  let V' := Submodule.span (FractionRing O) (Set.range v)
  have hBV : ∀ x ∈ B, x ∈ V' := by
    intro x hx
    have h1 : (⟨x, hx⟩ : B) ∈ Submodule.span O (Set.range b) := b.span_eq ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := B.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact Submodule.span_le_restrictScalars O (FractionRing O) _ h2
  have hV' : ∀ x ∈ V', f x ∈ V' := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => f x ∈ V') ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      exact hBV _ (hf _ (b i).2)
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact V'.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact V'.smul_mem a hx
  let f' := f.restrict hV'
  let bK : Module.Basis (Module.Free.ChooseBasisIndex O B) (FractionRing O) V' := Module.Basis.span hli
  haveI : FiniteDimensional (FractionRing O) V' := Module.Finite.of_basis bK
  set g := (f.restrictScalars O).restrict hf with hgdef
  have hmat : LinearMap.toMatrix bK bK f' = (LinearMap.toMatrix b b g).map (algebraMap O (FractionRing O)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have hg : (g (b j) : V) = ∑ i, b.repr (g (b j)) i • v i := by
      calc (g (b j) : V) = ((∑ i, b.repr (g (b j)) i • b i : B) : V) := by rw [b.sum_repr]
        _ = ∑ i, b.repr (g (b j)) i • v i := by simp only [Submodule.coe_sum, Submodule.coe_smul]; rfl
    have hf' : f' (bK j) = ∑ i, algebraMap O (FractionRing O) (b.repr (g (b j)) i) • bK i := by
      have hbK : ∀ i, (bK i : V) = v i := fun i => by rw [Module.Basis.span_apply]
      apply Subtype.ext
      simp only [f', LinearMap.restrict_apply, Submodule.coe_sum, Submodule.coe_smul]
      simp_rw [hbK]
      rw [show f (v j) = (g (b j) : V) from rfl, hg]
      simp [algebraMap_smul]
    rw [hf', bK.repr_sum_self]
  have hcp : (LinearMap.charpoly g).map (algebraMap O (FractionRing O)) = f'.charpoly := by
    rw [← LinearMap.charpoly_toMatrix g b, ← Matrix.charpoly_map, ← hmat, LinearMap.charpoly_toMatrix]
  rw [hcp]
  apply charpoly_eq_prod_of_iSup_eigenspace f' s
  have hle : V' ≤ LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) := by
    rw [GlobalTheory.JointDiag.ker_prod, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hs _ (b i).2
  rw [← GlobalTheory.JointDiag.ker_prod, LinearMap.ker_eq_top]
  ext y
  rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, GlobalTheory.JointDiag.aeval_restrict_coe]
  exact hle y.2

end GlobalTheory.HeightCounting.FormsStep

namespace GlobalTheory.HeightCounting.FormsStep

end GlobalTheory.HeightCounting.FormsStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterInvMulDiagEmbeddingEqCharDet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LiftBrg.LamKV

theorem coarse_single_eq_blkOf {a r t : ℕ} (hn : a = r + t) (i : Fin a) :
    Formalism.L2.Col.coarse r [t] i.val = Formalism.L2.DIV.blkOf r t i := by
  unfold Formalism.L2.DIV.blkOf
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have h1 : i.val - r < t := by omega
    have h2 : (i.val - r) / t = 0 := Nat.div_eq_of_lt h1
    rw [h2]
    simp [Formalism.L2.Col.blkIdx, h1]

theorem lamKV_inv_mul_diagEmb : ∀ {κ K : Type} [CommRing κ] [Field K] {a n r t : ℕ} (h : a = n) (hn : n = r + t) (hra : r ≤ a)
    (hrn : r ≤ n) (y : GL (Fin a) κ) (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) (χ : κˣ →* Kˣ)
    (hz : (LiftBrg.castGL h y)⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) ∈ Formalism.L2.Col.HKV κ n r t),
    Formalism.L2.Col.lamKV χ n r t ⟨_, hz⟩ = χ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 y) := by
  intro κ K _ _ a n r t h hn hra hrn y hy χ hz
  subst h
  have hc : LiftBrg.castGL (rfl : a = a) y = y := by
    ext i j
    simp [LiftBrg.castGL]
  have hf : (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) = Formalism.L2.DIV.blkOf r t :=
    funext (coarse_single_eq_blkOf hn)
  have hy' : y ∈ Formalism.L2.Col.blockUT a κ r [t] := by
    intro i j hij
    apply hy
    have hij' : (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) j < (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) i := hij
    rw [hf] at hij'
    exact hij'
  let Y : Formalism.L2.Col.blockUT a κ r [t] := ⟨y, hy'⟩
  let Dd : Formalism.L2.Col.blockUT a κ r [t] :=
    ⟨_, Formalism.L2.Col.diagEmb_mem_blockUT hrn [t] (Formalism.L2.DIV.upperLeftBlock hra y)⟩
  have hzz : (Subgroup.inclusion (Formalism.L2.Col.HK_le_blockUT a κ r [t]) ⟨_, hz⟩ : Formalism.L2.Col.blockUT a κ r [t]) = Y⁻¹ * Dd := by
    apply Subtype.ext
    show (LiftBrg.castGL (rfl : a = a) y)⁻¹ * _ = y⁻¹ * _
    rw [hc]
  have hD : Formalism.L2.Col.blkDet a κ (Formalism.L2.Col.coarse r [t]) 1 Dd = 1 := by
    apply Units.ext
    rw [Formalism.L2.Col.blkDet_val, Units.val_one]
    have : (Dd.1 : Matrix (Fin a) (Fin a) κ).toSquareBlock (fun i => Formalism.L2.Col.coarse r [t] i.val) 1 = 1 := by
      ext i j
      have hi : ¬ i.1.val < r := fun hi => by
        have := i.2
        simp only [Formalism.L2.Col.coarse_of_lt hi] at this
        exact absurd this (by decide)
      rw [Matrix.toSquareBlock_def, Matrix.of_apply]
      show Formalism.L2.Col.diagMat r a _ i.1 j.1 = _
      rw [Formalism.L2.Col.diagMat_of_not_left _ _ hi]
      simp only [Matrix.one_apply, Subtype.ext_iff]
    rw [this, Matrix.det_one]
  have hY : Formalism.L2.Col.blkDet a κ (Formalism.L2.Col.coarse r [t]) 1 Y = Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 y := by
    apply Units.ext
    rw [Formalism.L2.Col.blkDet_val, Formalism.L2.DIV.diag_block_det_val 1 hy]
    have key : ∀ b : Fin a → ℕ, b = Formalism.L2.DIV.blkOf r t →
        ((y : Matrix (Fin a) (Fin a) κ).toSquareBlock b 1).det =
          ((y : Matrix (Fin a) (Fin a) κ).submatrix (Subtype.val : {x : Fin a // Formalism.L2.DIV.blkOf r t x = 1} → Fin a)
            Subtype.val).det := by
      rintro b rfl
      rfl
    exact key _ hf
  rw [Formalism.L2.Col.lamKV, Formalism.L2.Col.lamK, MonoidHom.comp_apply, hzz, Formalism.L2.Col.detChar_apply]
  simp only [List.length_singleton, Finset.range_one, Finset.prod_singleton, zero_add]
  rw [map_mul, map_inv, hD, mul_one, hY, MonoidHom.inv_apply, map_inv, inv_inv]

end GlobalTheory.Mem.R3.LiftBrg.LamKV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeKeepsChartStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.move_down_level_prime_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → chOf ((I.fm l u a).dn i v c.1 g) = β := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
  exact GlobalTheory.Mem.Col2.TC.dn_keeps_chart I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownPointPreservesIndexFrames
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2

theorem PtY.mv_dn_facts {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n)
    (p : PtY ST SG Q y) (P : ST) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) (v : HeightOneSpectrum (𝓞 X.F))
    (hov : IsOver v P.1) (hne : conjPrime₂ P.1 ≠ P.1) (hconj : IsOver v (conjPrime₂ P.1)) :
    (p.mv (p.1.1.deco.dn P f')).1.2 = p.1.2 ∧ (p.mv (p.1.1.deco.dn P f')).1.1.fr = p.1.1.fr ∧
      Deco.SameOff ST SG v p.1.1.deco.1 (p.mv (p.1.1.deco.dn P f')).1.1.deco.1 := by
  classical

  have key : Deco.SameOff ST SG v p.1.1.deco.1 (p.1.1.deco.dn P f').1 := by
    unfold DecoSet.dn
    split_ifs with hok
    · refine ⟨fun Q hQ => ?_, fun Q hQ => ?_, fun _ _ => rfl⟩
      · have hQP : Q ≠ P.1 := fun h => hQ (by rw [h]; exact hov)
        have hQc : Q ≠ conjPrime₂ P.1 := fun h => hQ (by rw [h]; exact hconj)
        exact ((p.1.1.deco.2.dnN_spec P hne).2.2.1 Q hQP hQc).localization_eq.symm
      · have hQP : Q ≠ P := fun h => hQ (by rw [h]; exact hov)
        show p.1.1.deco.1.f Q = Function.update p.1.1.deco.1.f P f' Q
        rw [Function.update_of_ne hQP]
    · exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

  suffices H : ∀ d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG), Deco.SameOff ST SG v p.1.1.deco.1 d.1 →
      (p.mv d).1.2 = p.1.2 ∧ (p.mv d).1.1.fr = p.1.1.fr ∧
        Deco.SameOff ST SG v p.1.1.deco.1 (p.mv d).1.1.deco.1 from H _ key
  intro d hd
  by_cases h : (∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) ∧ p.1.2 ∈ y.ys d.1.N
  · have e : (p.mv d).1 = ((⟨(d, p.1.1.1.2), h.1⟩ : DecoF X.E n ST SG Q), p.1.2) :=
      congrArg Subtype.val (dif_pos h)
    rw [e]
    exact ⟨rfl, rfl, hd⟩
  · have e : p.mv d = p := dif_neg h
    rw [e]
    exact ⟨rfl, rfl, ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugate
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceOverSplit

theorem eq_or_eq_cP : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (s : SplitPlace D.host.E) (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal → Q = s.w ∨ Q = GlobalTheory.IdemSupport.cP s.w := by
  intro D _ s Q hQ
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE (D := D) s.w Q (hQ.trans s.w_under.symm) with e | e
  · exact Or.inl e
  · refine Or.inr (e.trans (HeightOneSpectrum.ext (Ideal.ext fun x => ?_)))
    rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.IdemSupport.mem_cP]
    have : IsCMField.ringOfIntegersComplexConj D.host.E x = GlobalTheory.IdemSupport.cO D x := by
      apply RingOfIntegers.ext
      rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.IdemSupport.cO_coe]
      rfl
    rw [this]

end GlobalTheory.PlaceOverSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionEqBasePiMulIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.PiDiv

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ST : Finset (Pl E)} {π : 𝓞 E}

theorem notMem_of_notMem (h : BasePi ST π) {w : Pl E} (hw : w ∉ ST) : π ∉ w.asIdeal := by
  intro hπ
  have hle : ST.inf (fun P : Pl E => P.asIdeal) ≤ w.asIdeal := by
    intro x hx
    have hx' : ∀ P ∈ ST, x ∈ P.asIdeal := fun P hP => (Finset.inf_le hP : ST.inf (fun P : Pl E => P.asIdeal) ≤ P.asIdeal) hx
    obtain ⟨c, rfl⟩ := (h.dvd x).1 hx'
    exact Ideal.mul_mem_right _ _ hπ
  obtain ⟨P, hP, hPw⟩ := (Ideal.IsPrime.inf_le' w.isPrime).1 hle
  have e : P.asIdeal = w.asIdeal := P.isMaximal.eq_of_le w.isPrime.ne_top hPw
  exact hw (HeightOneSpectrum.ext e ▸ hP)

theorem exp_neg_one_le (h : BasePi ST π) {w : Pl E} (hw : w ∈ ST) : WithZero.exp (-1) ≤ w.intValuation π := by
  classical
  obtain ⟨b, hb⟩ := w.intValuation_exists_uniformizer
  obtain ⟨a, ha⟩ := crtPl ST (fun P => if P = w then 1 else 0)
  have haw : a ∉ w.asIdeal := by
    intro haw
    have h1 := ha w hw
    rw [if_pos rfl] at h1
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.sub_mem _ haw h1))
  have hbw : b ∈ w.asIdeal := (w.intValuation_lt_one_iff_mem b).1 (by rw [hb, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
  have hab : ∀ P ∈ ST, a * b ∈ P.asIdeal := by
    intro P hP
    by_cases hPw : P = w
    · subst hPw; exact Ideal.mul_mem_left _ _ hbw
    · have h1 := ha P hP
      rw [if_neg hPw, sub_zero] at h1
      exact Ideal.mul_mem_right _ _ h1
  obtain ⟨c, hc⟩ := (h.dvd _).1 hab
  have hv : w.intValuation (a * b) = WithZero.exp (-1) := by
    rw [map_mul, hb, HeightOneSpectrum.intValuation_eq_one_iff.2 haw, one_mul]
  rw [← hv, hc, map_mul]
  exact mul_le_of_le_one_right' (w.intValuation_le_one c)

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem prV_inclE (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) x) = inclE (F := F) (v.adicCompletion F) x := by
  simp [prV, inclE, Algebra.TensorProduct.map_tmul]

end GlobalTheory.Mem.Col2.PiDiv


open GlobalTheory.Mem.Col2.PiDiv in
theorem GlobalTheory.Mem.Col2.prV_eq_pi_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), z ∈ Formalism.L2.Herm.intAf F E → (∀ P ∈ ST, Valued.v (adAt F P z) < 1) → ∃ s ∈ intV E v, prV (E := E) v z = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s := by
  intro F E _ _ _ _ _ _ ST π hπ v z hz hP
  set e : E := algebraMap (𝓞 E) E π with he_def
  have he : e ≠ 0 := hπ.coe_ne_zero
  have hzR : z ∈ RInt F E := hz
  refine ⟨prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e⁻¹ * z), ?_, ?_⟩
  · refine (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v _).2.2 fun w _ => ?_
    rw [map_mul, adAt_inclE, map_mul, valued_algebraMap, map_inv₀]
    have hz1 : Valued.v (adAt F w z) ≤ 1 := by rw [adAt_apply]; exact (mem_rInt_iff F E z).1 hzR w
    have hv0 : 0 < w.valuation E e := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 he
    rw [inv_mul_le_one₀ hv0]
    have hve : w.valuation E e = w.intValuation π := HeightOneSpectrum.valuation_of_algebraMap w π
    by_cases hw : w ∈ ST
    · exact (le_exp_neg_one_of_lt_one (hP w hw)).trans (hve ▸ exp_neg_one_le hπ hw)
    · rw [hve, HeightOneSpectrum.intValuation_eq_one_iff.2 (notMem_of_notMem hπ hw)]
      exact hz1
  · rw [map_mul, prV_inclE, ← mul_assoc, ← map_mul, mul_inv_cancel₀ he, map_one, one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAboveStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeProjection_zero_integral_iff_components_above : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (prV (E := E) v z = 0 ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → adAt F w z = 0) ∧ (prV (E := E) v z ∈ intV E v ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → Valued.v (adAt F w z) ≤ 1) := by
  first | exact @GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff | exact GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff | (intros; apply GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionConjFrameEqCastReductionAtLevelPrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

theorem castGL_rfl_apply' {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : castGL (rfl : m = m) x = x := by
  apply Units.ext
  ext i j
  simp [castGL]

theorem castGL_St_redFn (X : Stages) {m n : ℕ} (h : m = n) (x : GL (Fin m) (EA X)) (hx : x ∈ Formalism.L2.DIV.St 1)
    (PP : Pl X.toD7.host.E) :
    castGL h x ∈ Formalism.L2.DIV.St 1 ∧
      Formalism.L2.DIV.redFn 1 PP (castGL h x) = castGL h (Formalism.L2.DIV.redFn 1 PP x) := by
  subst h
  rw [castGL_rfl_apply', castGL_rfl_apply']
  exact ⟨hx, rfl⟩

theorem redZ_eq_castGL_redFn : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), LevOf X I U L →
    ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1),
      LiftBrg.ActQ.redZ X I U L i t A k κ w =
        LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.L2.DIV.redFn (L.βV i) w.1
          (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _))) := by
  intro X px I U L hL i t A k hF κ w
  have hAk : A * k ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X)) := Subgroup.mul_mem _ hF.2.1 hF.2.2.2.2.1
  have hred : Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) w.1 (A * k) = 1 := (Formalism.L2.DIV.mem_princAt.1 (hF.2.2.2.2.2 w.1 w.2)).2
  have hy := Formalism.L2.DIV.parLev_St (mem_parLev_of_Q X I U L i t κ)
  have hβ := hL.beta.1 i
  show Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) w.1
    ((A * k)⁻¹ * castGL (rkEq X i).symm
      (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) * (A * k)) = _
  generalize (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = y at hy ⊢
  generalize L.βV i = β at hy hβ ⊢
  subst hβ
  obtain ⟨hc, hcr⟩ := castGL_St_redFn X (rkEq X i).symm y hy w.1
  have e1 := Formalism.L2.DIV.redFn_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ hAk) hc) hAk w.1
  have e2 := Formalism.L2.DIV.redFn_mul (Subgroup.inv_mem _ hAk) hc w.1
  have e3 := Formalism.L2.DIV.redFn_inv hAk w.1
  refine e1.trans ?_
  rw [e2, e3, hred, hcr]
  simp

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLiftReadingOfDecoratedLatticePresentatioStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardLiftReading_of_decoratedLatticePresentations : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m), L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∀ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) →
    ∀ P : ∀ t, LiftBrg.PresL X I hX U Xg tr L cV i t, (∀ t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 (P t)) →
      (∀ t v, (P t).coef v = c v) → BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (P t).extL φ) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.brgStdV_of_readsStd_one | exact GlobalTheory.Mem.R3.LiftBrg.brgStdV_of_readsStd_one | (intros; apply GlobalTheory.Mem.R3.LiftBrg.brgStdV_of_readsStd_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportedAtConjPrimeIdempotentOfTrivialOffPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supportedAt_conjPrimeIdempotent_of_trivial_offPlace : ∀ {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → ∀ α : GA D V, α ∈ GfC V → (∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (finE V α) = 1) → SuppAt e V α := by
  first | exact @GlobalTheory.Mem.SuppOffPlace.suppAt_of_trivial_off | exact GlobalTheory.Mem.SuppOffPlace.suppAt_of_trivial_off | (intros; apply GlobalTheory.Mem.SuppOffPlace.suppAt_of_trivial_off <;> assumption)
end

