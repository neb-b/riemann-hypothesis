module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342

@[expose] public section

noncomputable section

section Loc
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.TopCongr GlobalTheory.LocMod
namespace GlobalTheory.Fam.TopFrames
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_right_invariant {a b : Type} [Fintype b] [DecidableEq b] {f : Matrix a b k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x)
    (hp : ∀ x y, IntM x → MaxM y → f (x + y) = f x) {g : Matrix b b k} (hg : MaxM (g - 1)) (x : Matrix a b k) :
    f (x * g) = f x := by
  by_cases hx : IntM x
  · have e : x * g = x + x * (g - 1) := by rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]
    rw [e, hp x _ hx (hx.mul_maxM hg)]
  · obtain ⟨u, hu, rfl⟩ := exists_mem_KOne hg
    have h1 : f x = 0 := by_contra fun h => hx (hs x h)
    have h2 : f (x * u.val) = 0 := by_contra fun h => hx (by
      have := (hs _ h).mul (mem_KO.1 (KOne_le_KO hu)).2
      rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this)
    rw [h1, h2]

theorem xiTop_mul_right [MeasurableSpace k] [BorelSpace k] {ν : Measure k} (hν : IsUnitVol ν) {s κ : ℕ} (S : SymData k s κ)
    (t : Type) [Fintype t] [DecidableEq t] {g : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k} (hg : MaxM (g - 1))
    (x : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k) :
    (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) (x * g) =
      (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) x := by
  refine mul_right_invariant (fun x hx => ?_) (fun x y hx hy => ?_) hg x
  · unfold Chain.xiTop at hx
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hx
    rintro (i | i) j
    · rw [phiTop_eq] at h1
      simpa using TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ t (s + 1)).symm i)
        ((stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl j))
    · exact by_contra fun h => h2 (hat_eq_zero S.cond hν (by simp) _ fun h' => h (h' j))
  · unfold Chain.xiTop
    have hxy := hx.add hy.intM
    rw [Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hx _), Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hxy _),
      phiTop_eq, phiTop_eq]
    congr 1
    · have e : fromCols (x + y).toRows₁ (0 : Matrix _ (Fin 0) k) = fromCols x.toRows₁ 0 + fromCols y.toRows₁ 0 := by
        ext i (j | j)
        · rfl
        · exact j.elim0
      rw [e, submatrix_add]
      refine TypeDatum.Phi_add _ (S.tame _) _ fun i j => ?_
      rw [submatrix_apply]
      rcases stdOrd (Fin κ) t (s + 1) 0 rfl j with j | j
      · exact hy _ _
      · exact j.elim0
    · have e : (x + y) (Sum.inr ()) = x (Sum.inr ()) + y (Sum.inr ()) := rfl
      rw [e, add_dotProduct, mul_add, AddChar.map_add_eq_mul, symmetricChain_psi_base_eq_one_of_maximalIdeal S t (hy _), mul_one]

theorem coords_near {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k n Y) (hF : IntM F.γ) {M : Matrix (Fin n) Y k}
    (hM : MaxM (M - F.β)) : MaxM (F.γ * M - 1) := by
  rw [← F.γβ, ← Matrix.mul_sub]
  exact hF.mul_maxM hM

theorem xiTop_frames [MeasurableSpace k] [BorelSpace k] {ν : Measure k} (hν : IsUnitVol ν) {s κ : ℕ} (S : SymData k s κ)
    (t : Type) [Fintype t] [DecidableEq t] {a b : ℕ} (FS : Frame k a (XIx (Fin κ) t (s + 1)))
    (FT : Frame k b (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit)) (hS : IntM FS.γ) (hT : IntM FT.γ) {β M} (hβ : MaxM (β - FS.β))
    (hM : MaxM (M - FT.β)) (z : Matrix (Fin b) (Fin a) k) {x} (hx : M * x = z * β) :
    (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) (FT.γ * z * FS.β) =
      (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) x := by
  have e : FT.γ * z * FS.β * (FS.γ * β) = FT.γ * M * x := by
    rw [Matrix.mul_assoc _ FS.β, ← Matrix.mul_assoc FS.β, FS.βγ, Matrix.one_mul, Matrix.mul_assoc, ← hx, Matrix.mul_assoc]
  rw [← xiTop_mul_right hν S t (coords_near FS hS hβ), e]
  exact xiTop_mul_congr k ν hν s κ S t _ (coords_near FT hT hM) x

end GlobalTheory.Fam.TopFrames
end Loc

section Gen
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.DetSpec Matrix
open GlobalTheory.SeeSaw.BaseFrame GlobalTheory.TopStep
namespace GlobalTheory.Fam.TopFrames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  [StarRing E] {hc : Formalism.BasicNotions.CMData F E}

theorem lift_near_of_lift {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} {k : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}
    {p₀ : DecoF E n ST SG Q'} (h : IsPtOf hc k p) (h₀ : IsPtOf hc k p₀) (hN : p₀.deco.1.N = stdLat E n) (w : SG)
    {g f : Sp E n ≃ₗ[E] Sp E n} (hg : IsLiftFr p.deco.1 w g)
    (hg1 : ∀ i j : Fin n, w.1.valuation E (g (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1)
    (hf : IsLiftFr p₀.deco.1 w f) (i j : Fin n) :
    w.1.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1 := by
  have key : ∀ (f : Sp E n ≃ₗ[E] Sp E n) i j, Valued.v (kMat w.1 (1 : GL (Fin n) (AfE F E)) f i j -
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j) =
      w.1.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) := fun f i j => by
    rw [kMat_one, Matrix.one_apply, if_congr (Fin.ext_iff (a := i) (b := j)) rfl rfl, ← valued_algebraMap,
      map_sub (algebraMap E (w.1.adicCompletion E)), apply_ite (algebraMap E _), map_one, map_zero]
  have h2 := val_kMat_sub_lt h w hg
  have h3 := val_kMat_sub_lt h₀ w hf
  rw [← one_mul k, kMat_mul] at h2 h3
  have hc1 : Formalism.L2.Herm.Carries (1 : GL (Fin n) (AfE F E)) (stdLat E n) (stdLat E n) := fun x => by simp
  have i1 := val_kMat_le (P := w.1) (f := 1) (hN ▸ h₀.lat : Formalism.L2.Herm.Carries k (stdLat E n) (stdLat E n)) fun _ => Iff.rfl
  have i2 := val_kMat_le (P := w.1) (f := f) hc1 (hN ▸ hf.1 : CharValCompare.IsFr w.1 (stdLat E n) f)
  rw [← key]
  exact near_right _ i2 (near_left _ i1 (fun i j => by rw [key]; exact hg1 i j) h2) h3 i j


omit [StarRing E] in
theorem intAt_sub_of_near {P : HeightOneSpectrum (𝓞 E)} {q : E} (hq : P.valuation E q = WithZero.exp (-1 : ℤ))
    {f : Sp E n ≃ₗ[E] Sp E n} (hf : ∀ i j : Fin n, P.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1)
    {y : Sp E n} (hy : ∀ i, IntAt P (q * y i)) (i : Fin n) : IntAt P (f y i - y i) := by
  have e : f y i - y i = ∑ j, (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) * y j := by
    simp only [_root_.sub_mul, Finset.sum_sub_distrib, ← Fin.ext_iff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [pi_eq_sum_univ' y, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [e]
  refine intAt_sum _ fun j _ => ?_
  have h1 := hy j
  rw [GlobalTheory.AtTypeExists.intAt_iff, map_mul] at h1 ⊢
  refine le_trans (mul_le_mul_left ?_ _) h1
  rw [hq]
  have h2 := hf i j
  generalize P.valuation E _ = v at h2
  by_cases h0 : v = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0] at h2 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
    rw [WithZero.exp_le_exp]
    omega

theorem isLiftFr_base [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (w : SG) :
    IsLiftFr (DecoF.base (E := E) (n := n) (ST := ST) (SG := SG) (Q := Q)).deco.1 w 1 :=
  ⟨fun _ => Iff.rfl, fun x hx => if_pos hx⟩


omit [StarRing E] in
theorem sumE_near {N : ℕ} (hN : N = n + 1) {P : HeightOneSpectrum (𝓞 E)} {t : Eˣ} (ht : P.valuation E ((t : E) - 1) < 1) (i j : Fin N) :
    P.valuation E (sumE hN (1 : Sp E n ≃ₗ[E] Sp E n) t (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1 := by
  rw [← if_congr (Fin.ext_iff (a := i) (b := j)) rfl rfl, ← Pi.single_apply j (1 : E) i]
  rcases idx_cases hN i with ⟨i, rfl⟩ | rfl
  · have := congrFun (prH_sumE hN (1 : Sp E n ≃ₗ[E] Sp E n) t (Pi.single j 1)) i
    rw [prH_apply] at this
    rw [this]
    show P.valuation E (_ - _) < 1
    rw [LinearEquiv.coe_one, id, prH_apply, sub_self, map_zero]
    exact zero_lt_one
  · rw [sumE_last, Pi.single_apply]
    split_ifs
    · rwa [mul_one]
    · simp

end GlobalTheory.Fam.TopFrames
end Gen

section World
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
namespace GlobalTheory.Fam.TopFrames

theorem prV_comm {D : D7} (v : GlobalTheory.FinPl.Pl D) (y : Af D.host.F ⊗[D.host.F] D.host.E) : Formalism.UG.prV (E := D.host.E) v
    ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom y) =
    (Algebra.TensorProduct.comm D.host.F (Fv D.host.F v) D.host.E).toAlgHom.toRingHom (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul x y => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem prV_eq_zero {D : D7} {Q : GlobalTheory.FinPl.Pl D → Prop} {x : AE D} (hx : x ∈ GlobalTheory.FinPl.idAt D Q) {v : GlobalTheory.FinPl.Pl D} (hv : ¬ Q v) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D x) = 0 := by
  rw [GlobalTheory.FinPl.idAt, Ideal.mem_inf, Ideal.mem_iInf] at hx
  have h := RingHom.mem_ker.1 (hx.2 ⟨v, hv⟩)
  refine (prV_comm v (finPart D x)).trans ?_
  rw [show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D x) = 0 from h, RingHom.map_zero]


set_option maxHeartbeats 1000000 in
theorem finM_map_prV {D : D7} (S : HSp D) {n : ℕ} (hn : S.rank = n) {Q : GlobalTheory.FinPl.Pl D → Prop} {h : GA D S}
    (hh : h ∈ GlobalTheory.FinPl.grpAt S Q) {v : GlobalTheory.FinPl.Pl D} (hv : ¬ Q v) : (finM S hn h).map (Formalism.UG.prV (E := D.host.E) v) = 1 := by
  subst hn
  rw [GlobalTheory.FinPl.grpAt, GlobalTheory.FinPl.SetCut.mem_congGrp_iff] at hh
  ext r s
  have key := prV_eq_zero (hh r s) hv
  have e1 : mt S h r s = (mt S h - 1) r s + (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) r s := by
    rw [Matrix.sub_apply, sub_add_cancel]
  simp only [finM, Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_refl, Equiv.refl_symm,
    Equiv.refl_apply]
  rw [e1, RingHom.map_add (f := _), RingHom.map_add (f := _), key, zero_add, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

section Tw
variable {u : B.Word} {a : I.ι} {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀}

theorem top_near (hI : I.Ok) (hA : A.Is) (P : BadPr I a) (hP : P.1 ∈ (B.primes X).vGs) {j : ℕ} (hj : j = B.R.m) (β : Ch₀ j) (r c) :
    HeightOneSpectrum.valuation B.fields.E P.1
      (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j β).1.1 P (Pi.single c 1) r - if r.val = c.val then 1 else 0) < 1 := by
  subst hj
  letI := GlobalTheory.Mem.Col2.starE B
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have h1 := B.R.two_le_m
    have h2 : B.R.N B.R.m = B.R.k + B.R.m * (B.R.t + 1) := rfl
    have h3 : B.R.m ≤ B.R.m * (B.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega⟩
  have hQ : ∀ Q : Formalism.L2.Col.QE I.sel (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K),
      (B.primes X).piT u ∉ Q.1.asIdeal := fun Q => ((TwistPrimes.twist_primes_away I hI).2 u a Q.1 Q.2).2.1
  have h1 := hA.top β (Formalism.L2.Col.DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _)
    ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩
  rw [one_mul] at h1
  have e : Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 B.R.m β).1.1 P = (A.p0 B.R.m β).1.1.deco.1.liftFr ⟨P.1, hP⟩ := dif_pos hP
  have hu := unitOf_val (Formalism.L2.Col.piT_notMem_vGs l.pr u ⟨P.1, hP⟩)
  rw [e]
  refine lift_near_of_lift h1 (hA.base _ le_rfl β).1 (hA.base _ le_rfl β).2 ⟨P.1, hP⟩
    (g := GlobalTheory.TopStep.sumE (Formalism.L2.Col.N_m_succ B.R) 1 (unitOf ((B.primes X).piT u))) ?_ (sumE_near _ ?_)
    (GlobalTheory.TopStep.liftFr_spec (A.p0 B.R.m β).1.1.deco.2 ⟨P.1, hP⟩) r c
  · rw [tilF_deco I.sel (I.tup a) l.pr u hQ]
    exact GlobalTheory.TopStep.isLiftFr_tilH _ _ (Formalism.L2.Col.conj_piT_notMem l.pr u) (Formalism.L2.Col.piT_notMem_vGs l.pr u) _
      (isLiftFr_base _) _ hu
  · obtain ⟨i, -, -, -, -, -, -, -, -, -, h⟩ := GlobalTheory.SeeSaw.LevelData.type_prime hP
    rw [hu]
    have h2 := (P.1.valuation_lt_one_iff_mem (K := B.fields.E) _).2 (h u)
    have h3 : ((X.piT u - 1 : 𝓞 B.fields.E) : B.fields.E) = ((B.primes X).piT u : B.fields.E) - 1 :=
      (algebraMap (𝓞 B.fields.E) B.fields.E).map_sub _ 1
    exact h3 ▸ h2

theorem intAt_q_mul (P : BadPr I a) (hP : P.1 ∈ (B.primes X).vGs) {j : ℕ} (hj : j + 1 = B.R.m) (β : Ch₀ j) (i) :
    Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : B.fields.E) *
      (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j β).1.1 P).symm (Formalism.L2.Col.repY (A.p0 j β).1.2) i) := by
  have h0 := (A.p0 j β).repY_mem hj
  obtain ⟨y, hy, hY⟩ := (A.p0 j β).mem_ybSet hj
  set z := Formalism.L2.Col.repY (A.p0 j β).1.2 with hz
  rw [hY] at h0
  have h1 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy P
  have h2 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 h0 P
  simp only [if_pos hP, zpow_zero, inv_one, one_smul, _root_.zpow_neg, inv_inv, zpow_one] at h1 h2
  have h3 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) • z ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (A.p0 j β).1.1.deco.1.N := by
    have h4 := add_mem h1 (Submodule.smul_mem _ ((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E) h2)
    convert h4 using 1
    rw [← algebraMap_smul B.fields.E ((Formalism.L2.Col.qOf P.1 : ℕ) : 𝓞 B.fields.E), map_natCast, ← smul_add, add_sub_cancel]
  rw [← (ptFr (A.p0 j β).1.1 P.1).apply_symm_apply (_ • z)] at h3
  have h5 := (isFr_ptFr (A.p0 j β).1.1 P.1 _).1 h3
  rw [← frsF_eq_ptFr I.sel (I.tup a), map_smul] at h5
  exact GlobalTheory.TopStep.mem_stdAt.1 h5 i

end Tw

variable {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}




end GlobalTheory.Fam.TopFrames
end World
end
