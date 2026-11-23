module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCombinationDependsOnProductFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CombDet

theorem row_position {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T} {p : Pair T}
    {I : Type} (S : Finset I) (e : AE D) (d : I → FinDatum G t p) (c : I → (WO (G.pS p) (G.pT p) →₀ ℂ))
    (hd : ∀ i ∈ S, (d i).e = e ∧ IsCombOf W (d i) (c i)) (f₀ : WO (G.pS p) (G.pT p) → ℂ)
    (h1 : IsThetaFunO W.ψ _ _ f₀)
    (h2 : IsLatVac (heisO W.ψ _ _) (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) f₀) :
    ∃ Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ), ∀ i ∈ S, comb W.ψ _ _ (c i) f₀ = Tm (d i).fn := by
  rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
  · exact ⟨0, fun i hi => by simp [hS] at hi⟩
  have key : ∀ i ∈ S, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀ (d i).fn (comb W.ψ _ _ (c i) f₀) := by
    intro i hi
    have h := (hd i hi).2.2.2 f₀ h1 h2
    have he := (hd i hi).1
    unfold FinDatum.IsTheta at h
    rw [he] at h
    exact h
  obtain ⟨Tm, hTm⟩ := (key i₀ hi₀).1
  exact ⟨Tm, fun i hi => (key i hi).2 Tm hTm⟩

def Spans {I Y : Type} (S : Finset I) (H : Y → I → ℂ) (g : I → ℂ) : Prop :=
  ∃ (J : Type) (P : Finset J) (a : J → ℂ) (y : J → Y), ∀ i ∈ S, g i = ∑ j ∈ P, a j * H (y j) i

theorem sum_prod_eq_zero {I ι : Type} [Fintype ι] {Y : ι → Type} (S : Finset I) (x : I → ℂ) (H : ∀ l, Y l → I → ℂ)
    (g : ι → I → ℂ) (hg : ∀ l, Spans S (H l) (g l)) (h : ∀ z : ∀ l, Y l, ∑ i ∈ S, x i * ∏ l, H l (z l) i = 0) :
    ∑ i ∈ S, x i * ∏ l, g l i = 0 := by
  classical
  choose J P a y hy using hg
  have e : ∀ i ∈ S, x i * ∏ l, g l i =
      ∑ z ∈ Fintype.piFinset P, (∏ l, a l (z l)) * (x i * ∏ l, H l (y l (z l)) i) := by
    intro i hi
    rw [Finset.prod_congr rfl fun l _ => hy l i hi, Finset.prod_univ_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [← Finset.mul_sum, h fun l => y l (z l), mul_zero]

theorem reproducing {I X : Type} (S : Finset I) (V : Submodule ℂ (X → ℂ)) (F : I → X → ℂ) (hF : ∀ i ∈ S, F i ∈ V) :
    ∃ (P : Finset X) (u : X → X → ℂ), (∀ x, u x ∈ V) ∧ ∀ i ∈ S, F i = ∑ x ∈ P, F i x • u x := by
  classical
  obtain ⟨P, u, hu⟩ := GlobalTheory.exists_finite_reproducing_of_submodule V
    (S.attach.image fun i : {i // i ∈ S} => (⟨F i.1, hF i.1 i.2⟩ : V))
  refine ⟨P, fun x => u x, fun x => (u x).2, fun i hi => ?_⟩
  have := congrArg V.subtype (hu ⟨F i, hF i hi⟩ (Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_attach _ _, rfl⟩))
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using this

theorem spans_linear {I X Z : Type} (S : Finset I) (F : I → X → ℂ) (Tm : (X → ℂ) →ₗ[ℂ] (Z → ℂ)) (z : Z) (g : I → ℂ)
    (hg : ∀ i ∈ S, g i = Tm (F i) z) : Spans S (fun x i => F i x) g := by
  obtain ⟨P, u, -, hu⟩ := reproducing S ⊤ F fun _ _ => trivial
  refine ⟨X, P, fun x => Tm (u x) z, id, fun i hi => ?_⟩
  rw [hg i hi]
  conv_lhs => rw [hu i hi]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, id]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

def vacSp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) Λ f}
  add_mem' := by
    intro f g hf hg
    have key : ∀ u, heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := fun u => by
      funext w; simp only [heisO, Pi.add_apply, mul_add]
    refine ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_add hf.1 hg.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [key, hf.2.1 u hu, hg.2.1 u hu]
    · rw [key, hf.2.2 e he u hu hh, hg.2.2 e he u hu hh]
  zero_mem' := ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T, fun u _ => by funext w; simp [heisO],
    fun e _ u _ _ => by funext w; simp [heisO]⟩
  smul_mem' := by
    intro c f hf
    have key : ∀ u, heisO ψ S T u (c • f) = c • heisO ψ S T u f := fun u => by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    refine ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c hf.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [key, hf.2.1 u hu]
    · rw [key, hf.2.2 e he u hu hh]

theorem col_position {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T} (j : ℕ)
    {I : Type} (S : Finset I) (e : AE D) (d₁ : I → FinDatum G t (.top t j)) (d₂ : I → FinDatum G t (.top t (j + 1)))
    (c₁ : I → (WO (G.V (.top j)) (G.V (.top (j + 1))) →₀ ℂ)) (c₂ : I → (WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) →₀ ℂ))
    (h₁ : ∀ i ∈ S, (d₁ i).e = e ∧ IsCombOf W (d₁ i) (c₁ i)) (h₂ : ∀ i ∈ S, (d₂ i).e = e ∧ IsCombOf W (d₂ i) (c₂ i))
    (C : WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ)
    (hC : IsBiVac W.ψ _ _ _ (G.Λ (.top j) : Set _) (G.Λ (.top (j + 1)) : Set _) (G.Λ (.top (j + 1 + 1)) : Set _) C) (u v) :
    Spans S (fun (p : WO (G.V (.top j)) (G.V (.top (j + 1))) × WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1)))) i =>
      (d₁ i).fn p.1 * (d₂ i).fn p.2) fun i => biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v := by
  classical
  choose Tu hTu using fun u' => row_position W S e d₂ c₂ h₂ (C u') (hC.right u').1 (hC.right u').2
  let Lm : (WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ) →ₗ[ℂ] (WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ) :=
    LinearMap.pi fun u' => (LinearMap.proj v) ∘ₗ Tu u'
  let Vac := vacSp W.ψ _ _ (latO (G.V (.top j)) (G.V (.top (j + 1))) (G.Λ (.top j) : Set _) (G.Λ (.top (j + 1)) : Set _) fun _ => True)
  have hL : ∀ i ∈ S, Lm (d₂ i).fn = fun u' => comb W.ψ _ _ (c₂ i) (C u') v := fun i hi => by
    funext u'
    exact (congrFun (hTu u' i hi) v).symm
  have hV : ∀ i ∈ S, (d₂ i).fn ∈ Vac.comap Lm := fun i hi => by
    rw [Submodule.mem_comap, hL i hi]
    have : (fun u' => comb W.ψ _ _ (c₂ i) (C u') v) =
        ∑ b ∈ (c₂ i).support, ((c₂ i) b * W.ψ (symplOH _ _ v b)) • fun u' => C u' (v + b) := by
      funext u'
      simp only [GlobalTheory.BiCombStable.comb_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [this]
    exact Vac.sum_mem fun b _ => Vac.smul_mem _ (hC.left (v + b))
  obtain ⟨P, ε, hε, hP⟩ := reproducing S (Vac.comap Lm) (fun i => (d₂ i).fn) hV
  choose Tx hTx using fun x => row_position W S e d₁ c₁ h₁ (Lm (ε x)) (hε x).1 (hε x).2
  obtain ⟨Q, η, -, hQ⟩ := reproducing S ⊤ (fun i => (d₁ i).fn) fun _ _ => trivial
  refine ⟨_, Q ×ˢ P, fun p => Tx p.2 (η p.1) u, id, fun i hi => ?_⟩
  have e1 : biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v = GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (d₂ i).fn) u := by
    rw [hL i hi]; rfl
  have e2 : ∀ x, GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (ε x)) = ∑ q ∈ Q, (d₁ i).fn q • Tx x (η q) := fun x => by
    refine (hTx x i hi).trans ?_
    refine (congrArg (Tx x) (hQ i hi)).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  have e3 : GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (d₂ i).fn) =
      ∑ x ∈ P, (d₂ i).fn x • GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (ε x)) := by
    refine (congrArg (fun f => GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm f)) (hP i hi)).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  show biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v = _
  rw [e1, e3, Finset.sum_product_right, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [e2, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, id]
  ring

theorem prod_range_pairs (f : ℕ → ℂ) (n : ℕ) :
    ∏ j ∈ Finset.range (2 * n), f j = ∏ k ∈ Finset.range n, f (2 * k) * f (2 * k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ, mul_assoc]

theorem sum_evT_eq_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (ρ : RealMatch W)
    (t : T) (e : AE D) (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat G t) (c : I → Combs G)
    (hd : ∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf W ((d i).1 j) ((c i).1 j)) ∧
      ∀ n, ((d i).2 n).e = e ∧ IsCombOf W ((d i).2 n) ((c i).2 n))
    (h : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) (y : RowPt G), (∀ j, IsHalf e (u j)) →
      (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0)
    (C : BiFam G) (hC : IsRealFam W C) (u : ColPt G) (y : RowPt G) :
    ∑ i ∈ S, x i * evT (combC W (c i) C) (combR ρ (c i)) u y = 0 := by
  classical
  have hm : 0 + 2 * ((D.R.m - 2) / 2) + 2 = D.R.m := top_idx
  have h' : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) (y : RowPt G),
      ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0 := by
    intro u y
    by_cases hu : ∀ j, IsHalf e (u j)
    · by_cases hy : ∀ n, IsHalf e (y n)
      · exact h u y hu hy
      · obtain ⟨n, hn⟩ := not_forall.1 hy
        refine Finset.sum_eq_zero fun i hi => ?_
        have h0 : ((d i).2 n).fn (y n) = 0 := by
          by_contra h0
          exact hn (((hd i hi).2 n).1 ▸ ((d i).2 n).sb.1 _ h0)
        rw [Finset.prod_eq_zero (f := fun n => ((d i).2 n).fn (y n)) (Finset.mem_univ n) h0, mul_zero, mul_zero]
    · obtain ⟨j, hj⟩ := not_forall.1 hu
      refine Finset.sum_eq_zero fun i hi => ?_
      have h0 : ((d i).1 j).fn (u j) = 0 := by
        by_contra h0
        exact hj (((hd i hi).1 j).1 ▸ ((d i).1 j).sb.1 _ h0)
      rw [Finset.prod_eq_zero (f := fun j => ((d i).1 j).fn (u j)) (Finset.mem_univ j) h0, zero_mul, mul_zero]

  have hrow : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))),
      ∑ i ∈ S, (x i * ∏ j, ((d i).1 j).fn (u j)) * ∏ n, combR ρ (c i) n (y n) = 0 := by
    intro u
    refine sum_prod_eq_zero S _ (fun (n : Fin D.R.m) (z : WO (G.pS (.chi n D.R.m : Pair T)) (G.pT (.chi n D.R.m : Pair T))) i =>
      ((d i).2 n).fn z) (fun n i => combR ρ (c i) n (y n)) (fun n => ?_) fun z => ?_
    · have hv := ρ.vX_is n D.R.m n.2 le_rfl
      obtain ⟨Tm, hTm⟩ := row_position W S e (fun i => (d i).2 n) (fun i => (c i).2 n) (fun i hi => (hd i hi).2 n) _
        hv.2.theta hv.2.lat
      exact spans_linear S (fun i => ((d i).2 n).fn) Tm (y n) _ fun i hi => congrFun (hTm i hi) (y n)
    · simpa only [mul_assoc] using h' u z

  let F : I → ∀ j : ℕ, WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ := fun i j =>
    if hj : j < D.R.m then ((d i).1 ⟨j, hj⟩).fn else 0
  have hcol := sum_prod_eq_zero (ι := Fin (D.R.m / 2)) S (fun i => x i * ∏ n, combR ρ (c i) n (y n))
    (fun k (w : ColPt G) i => F i (2 * k) (w (2 * k)) * F i (2 * k + 1) (w (2 * k + 1)))
    (fun k i => combC W (c i) C (2 * k) (u (2 * k)) (u (2 * k + 1))) (fun k => ?_) fun z => ?_
  · rw [← hcol]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evT, Finset.prod_range]
    ring
  · have k0 : 2 * (k : ℕ) < D.R.m := by have := k.2; omega
    have k1 : 2 * (k : ℕ) + 1 < D.R.m := by have := k.2; omega
    obtain ⟨J, P, a, p, hp⟩ := col_position W (2 * k) S e (fun i => (d i).1 ⟨2 * k, k0⟩) (fun i => (d i).1 ⟨2 * k + 1, k1⟩)
      (fun i => (c i).1 (2 * k)) (fun i => (c i).1 (2 * k + 1)) (fun i hi => (hd i hi).1 ⟨2 * k, k0⟩)
      (fun i hi => (hd i hi).1 ⟨2 * k + 1, k1⟩) (C (2 * k)) (hC _ (even_two_mul _) k0).1 (u (2 * k)) (u (2 * k + 1))
    refine ⟨J, P, a, fun j => Function.update (Function.update (0 : ColPt G) (2 * k) (p j).1) (2 * k + 1) (p j).2,
      fun i hi => (hp i hi).trans (Finset.sum_congr rfl fun j _ => ?_)⟩
    simp only [F, dif_pos k0, dif_pos k1, Function.update_self,
      Function.update_of_ne (show 2 * (k : ℕ) ≠ 2 * k + 1 by omega)]
  · let w : ColPt G := fun j => if hj : j / 2 < D.R.m / 2 then z ⟨j / 2, hj⟩ j else 0
    have hw : ∀ (k : Fin (D.R.m / 2)) (j : ℕ), j / 2 = (k : ℕ) → w j = z k j := by
      rintro ⟨k, hk⟩ j hj
      have hj' : j / 2 = k := hj
      subst hj'
      exact dif_pos hk
    rw [← hrow fun j => w j]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : ∏ j : Fin D.R.m, ((d i).1 j).fn (w j) = ∏ j ∈ Finset.range D.R.m, F i j (w j) := by
      rw [Finset.prod_range]
      exact Finset.prod_congr rfl fun j _ => by simp only [F, dif_pos j.2]
    have e2 : Finset.range D.R.m = Finset.range (2 * (D.R.m / 2)) := by congr 1; omega
    rw [e1, e2, prod_range_pairs (fun j => F i j (w j)), Finset.prod_range,
      Finset.prod_congr rfl fun (k : Fin (D.R.m / 2)) _ => show F i (2 * k) (w (2 * k)) * F i (2 * k + 1) (w (2 * k + 1)) =
        F i (2 * k) (z k (2 * k)) * F i (2 * k + 1) (z k (2 * k + 1)) by
          rw [hw k _ (by omega), hw k _ (by omega)]]
    ring

theorem comb_det : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t e, IsIdemSum e (locPl ch.G t) → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat ch.G t) (c : I → Combs ch.G), (∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf ch.W ((d i).1 j) ((c i).1 j)) ∧ ∀ n, ((d i).2 n).e = e ∧ IsCombOf ch.W ((d i).2 n) ((c i).2 n)) → (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : RowPt ch.G), (∀ j, IsHalf e (u j)) → (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0) → ∀ C, IsRealFam ch.W C → ∀ u y, ∑ i ∈ S, x i * evT (combC ch.W (c i) C) (combR ch.rm (c i)) u y = 0 :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ t e _ I S x d c hd h C hC u y =>
    sum_evT_eq_zero ch.W ch.rm t e I S x d c hd h C hC u y⟩⟩

end GlobalTheory.CombDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestExistsCombinationsOfExpansion
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CombsExist

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum


set_option maxHeartbeats 1000000 in
theorem exists_comb_model {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D)
    (Φ : WO S T → ℂ) (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (he : e * e = e)
    (hec : e * cA D e = 0) (hinf : infPart D e = 0)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ) :
    ∃ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0 ∧ IsHalf (e + cA D e) u) ∧ ∀ f₀ Tm,
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
        (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
      comb ψ S T c f₀ = Tm Φ := by
  classical
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hce : cA D e * e = 0 := by rw [mul_comm, hec]
  have half1 : ∀ u : WO S T, IsHalf e u → IsHalf (e + cA D e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have half2 : ∀ u : WO S T, IsHalf (cA D e) u → IsHalf (e + cA D e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S T ψ
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin' Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    refine ⟨ψ (symplOH S T x y) • Finsupp.single (x + y) 1, fun u hu => ?_, fun f₀ Tm hTm => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset (Finsupp.support_smul hu))]
      have h1 := infPart_of_half hinf ((isHalf_iff S T).2 hx)
      have h2 := infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy)
      refine ⟨?_, fun i j => ?_⟩
      · ext i j
        have a1 := congrFun (congrFun h1 i) j
        have a2 := congrFun (congrFun h2 i) j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at a1 a2 ⊢
        rw [RingHom.map_add (f := _), a1, a2, add_zero]
      · rw [Matrix.add_apply, mul_add, half1 x ((isHalf_iff S T).2 hx) i j, half2 y ((isHalf_iff S T).2 hy) i j]
    have s0 := GlobalTheory.isSBHalf_halfInd e (latO S T ΛS ΛT fun _ => True)
    have s1 : IsSBHalf e (latO S T ΛS ΛT fun _ => True)
        fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e (latO S T ΛS ΛT fun _ => True) (t + (k * k') • u) =
            halfInd e (latO S T ΛS ΛT fun _ => True) t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := hTm.vac
    rw [one_smul] at v1
    rw [e1, hTm.trans _ s1 x ((isHalf_iff S T).2 hx), hTm.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    have hxy := heisL_heisL S T ψ x y f₀
    change heisO ψ S T x (heisO ψ S T y f₀) = ψ (symplOH S T x y) • heisO ψ S T (x + y) f₀ at hxy
    rw [hxy, GlobalTheory.LocComb.comb_smul, GlobalTheory.LocComb.comb_single]
  | zero => exact ⟨0, by simp, fun f₀ Tm _ => by rw [LinearMap.map_zero]; simp [comb]⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨c, h1, h2⟩ := hg
    obtain ⟨c', h1', h2'⟩ := hg'
    exact ⟨c + c', fun w hw => (Finset.mem_union.1 (Finsupp.support_add hw)).elim (h1 w) (h1' w), fun f₀ Tm h => by
      rw [LinearMap.map_add (f := _), GlobalTheory.LocComb.comb_add, h2 f₀ Tm h, h2' f₀ Tm h]⟩
  | smul a g _ hg =>
    obtain ⟨c, h1, h2⟩ := hg
    exact ⟨a • c, fun w hw => h1 w (Finsupp.support_smul hw), fun f₀ Tm h => by
      rw [LinearMap.map_smul, GlobalTheory.LocComb.comb_smul, h2 f₀ Tm h]⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T}

theorem exists_isCombOf {p : Pair T} (hS : IsSelfDualC (G.pS p) (G.latS p)) (hT : IsSelfDualC (G.pT p) (G.latT p))
    (d : FinDatum G t p) : ∃ c, IsCombOf W d c := by
  obtain ⟨c, h1, h2⟩ := exists_comb_model W.ψ _ _ _ _ d.e d.fn W.ψ_std hS hT (idemSum_mul_self d.e_is) d.e_is.2
    (infPart_idemSum d.e_is) d.sb
  exact ⟨c, fun u hu => (h1 u hu).1, fun u hu => (h1 u hu).2, fun f₀ hth hvac =>
    ⟨(GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ hS hT d.P d.e d.e_is f₀ hth hvac).1, h2 f₀⟩⟩

theorem exists_isCombs {μ₀ : T} (hL : L.Is μ₀) (τ : PureDat G t →₀ ℂ) : ∃ c, IsCombs W τ c := by
  have sdT : ∀ j, j ≤ D.R.m → IsSelfDualC (G.V (.top j)) (G.Λ (.top j)) := fun j hj =>
    (G.isV (X := .top j) hj fun _ h => by cases h).sd
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i D.R.m)) (G.Λ (.grid i D.R.m)) := fun i hi => by
    cases i with
    | zero => exact (colY_isV D T L μ₀ hL D.R.m le_rfl).sd
    | succ i => exact (G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ fun _ h => by cases h).sd
  choose c₁ h₁ using fun (d : PureDat G t) (j : Fin D.R.m) =>
    exists_isCombOf W (p := .top t j) (sdT j j.2.le) (sdT (j + 1) j.2) (d.1 j)
  choose c₂ h₂ using fun (d : PureDat G t) (i : Fin D.R.m) =>
    exists_isCombOf W (p := .chi i D.R.m) (isSelfDualC_neg (sdG (i + 1) i.2)) (sdG i i.2.le) (d.2 i)
  refine ⟨fun d => (fun j => if h : j < D.R.m then c₁ d ⟨j, h⟩ else 0, c₂ d), fun d _ => ⟨fun j => ?_, h₂ d⟩⟩
  dsimp only
  rw [dite_eq_left j.2]
  exact h₁ d j

theorem combs_exist : Big fun ch => ∀ t Φ β τ, ch.S.IsExpansion t Φ β τ → ∃ c, IsCombs ch.W τ c :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ _ _ _ τ _ => exists_isCombs ch.W s.core.lev τ⟩⟩

end GlobalTheory.CombsExist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLastColumnLevelIffGridVertexLevelVolumeOn
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLevelUnit

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem levJ_grid_succ (G : GridData L sc) (t : T) (i n : ℕ) (hn : n ≠ 0) :
    levJ G t (.grid (i + 1) n) = G.levMax (.grid (i + 1) n) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n => rfl

theorem levJ_grid_zero (G : GridData L sc) (t : T) (n : ℕ) (hn : n ≠ 0) :
    HEq (levJ G t (.grid 0 n)) (levCol L t (n - 1)) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n => exact HEq.rfl

theorem levRow_iff_levJ : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t i (hi : i ≤ D.R.m) (k : FinPt ch.G (.grid i D.R.m)), finG (ch.G.V (.grid i D.R.m)) k ∈ ch.S.toGridChoice.levRow t i hi ↔ finG (ch.G.V (.grid i D.R.m)) k ∈ levJ ch.G t (.grid i D.R.m) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t i hi k => by
    have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
    have hU : finG (ch.G.V (.grid i D.R.m)) k ∈ UA D.sp.cm (ch.G.V (.grid i D.R.m)).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
    suffices e : ch.S.toGridChoice.levRow t i hi ⊓ UA D.sp.cm (ch.G.V (.grid i D.R.m)).gram = levJ ch.G t (.grid i D.R.m) by
      rw [← e]; exact ⟨fun h => ⟨h, hU⟩, fun h => h.1⟩
    clear hU k
    cases i with
    | zero =>
      apply eq_of_heq
      exact (_root_.GlobalTheory.FunObj.levRow_zero_eq_lev ch.W ch.S.toGridChoice s.core.lev t hi).trans
        ((levJ_grid_zero ch.G t D.R.m hm).trans (levCol_top _ t (j := D.R.m - 1) (by omega))).symm
    | succ i =>
      rw [levJ_grid_succ ch.G t i D.R.m hm]
      exact GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA ch.W ch.S.toGridChoice t i hi⟩⟩

end GlobalTheory.RowLevelUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualModulusShiftHomLatticeOwnAnnihilator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.AscFin.latBig_ann_right : OnStd fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∀ u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u' → (∀ u ∈ latBig G i, W.ψ (symplO _ _ u u') = 1) → u' ∈ latBig G i := by
  intro D hq T L μ0 hL sc G W M hM F hF i hi u' hmx h
  have sdS : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) :=
    (G.isV (X := .grid (i + 1) 0) ⟨by omega, Nat.zero_le _⟩ (fun j hj => by injection hj with e1 e2; omega)).sd
  have sdT : IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) :=
    ((_root_.GlobalTheory.AscFin.GridLat.lattices_grid D hq T L μ0 hL sc G W M hM F hF).1 i hi).2.2.2
  refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdT (fun _ => True) u' hmx).2 fun u hu => ?_
  rw [GlobalTheory.SplitScalar.symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
end

