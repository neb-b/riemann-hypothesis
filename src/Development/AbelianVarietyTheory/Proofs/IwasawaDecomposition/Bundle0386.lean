module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpKeepsChart
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

section SameUp

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem SameG.up' {y : Ys X n} (p : PtY ST SG Q y) (P : ST) (hP : MoveHyp ST SG P) (q : 𝓞 X.E) {x : Sp X.E n}
    (hx : x ∈ p.1.1.deco.1.N) : SameG p (p.mv (p.1.1.deco.up P q x)) := by
  classical
  have hs : DecoSet.SameOn SG p.1.1.deco (p.1.1.deco.up P q x) :=
    DecoSet.sameOn_up _ P hP.ne (fun w hw => hP.sg ⟨w, hw⟩) q hx
  have hb : (p.1.1.deco.up P q x).1.be = p.1.1.deco.1.be := by
    unfold DecoSet.up
    split_ifs with h
    · rfl
    · rfl
  by_cases h : (∀ (w : Q) (z : Sp X.E n), p.1.1.1.2 w z ∈ (p.1.1.deco.up P q x).1.at w.1 ↔ z ∈ stdAt X.E n w.1) ∧ p.1.2 ∈ y.ys (p.1.1.deco.up P q x).1.N
  · have e : p.mv (p.1.1.deco.up P q x) = ⟨(⟨(p.1.1.deco.up P q x, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ := dif_pos h
    rw [e]
    exact ⟨rfl, rfl, fun w => hs w.1 w.2, hb⟩
  · have e : p.mv (p.1.1.deco.up P q x) = p := dif_neg h
    rw [e]
    exact SameG.refl p

end SameUp

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem TC.cosetIn_rep_up (hX : B.fields.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (i : ℕ) (v : (B.primes X).vT u)
    (c : (I.stp u a i).Cl) (x : ((I.atIn u a).A i).lv v c) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (((I.atIn u a).A i).upPt v c x))) =
      cosetIn ((I.stp u a i).rep c) := by
  by_cases hj : i + 1 = B.R.m
  · refine GStep.prefRep_eq_of_normal (I.stp0 u a i) c.1 (fun q' : (I.stp0 u a i).D c.1 => cosetIn q') (I.pref u a i c.1)
      (GStep.prefRep_normal (I.stp0 u a i) c.1 _ _ (fun p hp => hp.2.1 hj) (I.pref_of_normalFor u a i hj c.1)) c.2 _ fun h => ?_
    have r : SameG ((I.stp u a i).rep c) (((I.atIn u a).A i).upPt v c x) :=
      SameG.up' ((I.stp u a i).rep c) v (moveHyp_of_ok hPr u v) _ (Quotient.out x).2
    apply cosetIn_eq_of_sameG hX hPr
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact congrArg (fun F => fun P => (FrmG.incl _ _ h).1.1 * F P * ((FrmG.incl _ _ h).2.2 P)⁻¹.1) r.fr
    · exact congrArg (fun S => (fun v => h.1.1 v) '' S) r.ys
    · intro w
      have locP_gmap_eq_of_locP_eq {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
          (g : Sp E n ≃ₗ[E] Sp E n) {N N' : Submodule (𝓞 E) (Sp E n)}
          (h : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) :
          Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N') = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N) := by
        have hs : ∀ (s : 𝓞 E) (z : Sp E n), g.symm (s • z) = s • g.symm z := fun s z =>
          ((g.symm : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)).map_smul s z
        have hmemL : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
            x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ M := fun _ _ => Iff.rfl
      
        have hmemg : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
            x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g M) ↔ g.symm x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M := by
          intro M x
          rw [hmemL, hmemL]
          constructor
          · rintro ⟨s, hs0, hx⟩
            obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
            have hz' : z = g.symm (s • x) := by
              rw [← hzx]
              simp
            exact ⟨s, hs0, by rw [← hs, ← hz']; exact hz⟩
          · rintro ⟨s, hs0, hx⟩
            refine ⟨s, hs0, Submodule.mem_map.mpr ⟨g.symm (s • x), by rw [hs]; exact hx, by simp⟩⟩
        ext x
        rw [hmemg, hmemg, h]
      exact locP_gmap_eq_of_locP_eq w.1 h.1.1 (r.at_eq w)
    · exact congrArg (fun B => fun w x => ((FrmG.incl _ _ h).2.1 w).1.mulVec (B w (h.1.1.symm x))) r.be
  · have h0 : ∀ q : PtAt B.R I.sel (I.tup a) (I.cst a) u i, cosetIn q = fun _ => ∅ := by
      intro q
      funext P
      have hq : q.1.2 = ∅ := by
        have := q.2
        rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj] at this
        exact this
      ext z
      simp [cosetIn, hq]
    rw [h0, h0]

end GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem TC.up_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.ReadsK l Z u a i hi chOf K → ∀ (v : (I.atT l u a).vT) (c : (I.chain l u a).cls i) (x : (I.fm l u a).lv i v c), (I.fm l u a).fv i v c x = 1 → chOf ((I.fm l u a).up i v c x) = chOf c := by
  intro B X I _ _ l Z u a i hi bad Ch chOf K hR v c x _
  obtain ⟨k, hk⟩ := hR
  have hX : B.fields.Ok := (base_fields_primes_ok B X).1
  exact (hk.key ((I.fm l u a).up i v c x) c).2 ⟨rfl, I.cosetIn_rep_up hX l.pr u a i v c x⟩

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperParahoricCharacterInvEqInvDetBlock
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.LamQInv

theorem coarseBlockIndex_single_eq_twoBlock {a r b : ℕ} (hn : a = r + b) (i : Fin a) :
    Formalism.L2.Col.coarse r [b] i.val = Formalism.L2.DIV.blk2 r i := by
  unfold Formalism.L2.DIV.blk2
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have : i.val - r < b := by omega
    simp [Formalism.L2.Col.blkIdx, this]

theorem lamQ_castGL_inv : ∀ {κ K : Type} [CommRing κ] [Field K] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (χ : κˣ →* Kˣ)
    (hz : (LiftBrg.castGL h y)⁻¹ * 1 ∈ Formalism.L2.Col.HQ κ n r b),
    Formalism.L2.Col.lamQ χ n r b ⟨_, hz⟩ = (χ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 y))⁻¹ := by
  intro κ K _ _ a n r b h hn y hy χ hz
  subst h
  have hc : LiftBrg.castGL (rfl : a = a) y = y := by
    ext; simp [LiftBrg.castGL]
  have hy' : y ∈ Formalism.L2.Col.blockUT a κ r [b] := by
    intro i j hij
    apply hy
    show Formalism.L2.DIV.blk2 r j < Formalism.L2.DIV.blk2 r i
    rw [← coarseBlockIndex_single_eq_twoBlock hn, ← coarseBlockIndex_single_eq_twoBlock hn]
    exact hij
  have he : (⟨_, hz⟩ : ↥(Formalism.L2.Col.HQ κ a r b)) = (⟨y, hy'⟩ : ↥(Formalism.L2.Col.HQ κ a r b))⁻¹ := by
    ext1
    simp [hc]
  rw [he, map_inv, Formalism.L2.Col.lamQ_apply]
  congr 2
  ext
  rw [Formalism.L2.Col.blkDet_val, Formalism.L2.DIV.diag_block_det_val 1 hy]
  rw [Matrix.toSquareBlock_def]
  let e : {i : Fin a // Formalism.L2.Col.coarse r [b] i.val = 1} ≃ {i : Fin a // Formalism.L2.DIV.blk2 r i = 1} :=
    Equiv.subtypeEquivRight (fun i => by rw [coarseBlockIndex_single_eq_twoBlock hn])
  exact Matrix.det_submatrix_equiv_self e (((y : GL (Fin a) κ) : Matrix (Fin a) (Fin a) κ).submatrix (Subtype.val : {i : Fin a // Formalism.L2.DIV.blk2 r i = 1} → Fin a) Subtype.val)

end GlobalTheory.Mem.R3.LiftBrg.LamQInv
end
end

