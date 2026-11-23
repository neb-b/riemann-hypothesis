module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCharacterTranslatesCoinvariant
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.RankFibre

def stabSub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hg]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem of_parts (Lirr : (GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M)) (Llaw : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ), GlobalTheory.RankFibre.fibre ν β a b Φ ∈ GlobalTheory.PRep.indSpace (GlobalTheory.SmGL.parab k (GlobalTheory.RankFibre.blocks a b)) (GlobalTheory.SmGL.ofChar (GlobalTheory.RankFibre.parChar ν β a b)))) (Lsmooth : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ})) (Linteg : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), MeasureTheory.Integrable (fun g : GL (Fin a) k => Φ (g.val * GlobalTheory.SplitFlip.X0 k finSumFinEquiv) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))))) (Lker : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b))) : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) := by
  intro HB k _ _ _ _ a d had ν β hνs hνu hβs hβu N hCN hNSB hNst
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le had
  borelize k

  have hS0 : ∀ (h : GL (Fin (a + b)) k) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
      Φ ∈ fullRankSB k a (a + b) → omA ν β 1 h Φ ∈ fullRankSB k a (a + b) := by
    intro h Φ hΦ
    refine ⟨omA_mem_SB ν β 1 h hΦ.1, fun Y hY => ?_⟩
    have hr : (((1 : GL (Fin a) k)⁻¹).val * Y * (invT h).val).rank ≠ a := by
      rwa [inv_one, Units.val_one, Matrix.one_mul,
        Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units (invT h))]
    simp only [omA, hΦ.2 _ hr, mul_zero]

  have hint : ∀ Φ ∈ fullRankSB k a (a + b), ∀ x : GL (Fin (a + b)) k,
      Integrable (fun g : GL (Fin a) k => omA ν β 1 x Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
        apow (gdet g) (((a + b : ℕ) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) :=
    fun Φ hΦ x => Linteg k a b ν hνs _ (hS0 x Φ hΦ)
  have hadd : ∀ Φ ∈ fullRankSB k a (a + b), ∀ Ψ ∈ fullRankSB k a (a + b),
      fibre ν β a b (Φ + Ψ) = fibre ν β a b Φ + fibre ν β a b Ψ := by
    intro Φ hΦ Ψ hΨ
    funext x
    rw [Pi.add_apply]
    unfold fibre
    rw [← integral_add (hint Φ hΦ x) (hint Ψ hΨ x)]
    congr 1
    funext g
    simp only [omA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsmul : ∀ (c : ℂ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
      fibre ν β a b (c • Φ) = c • fibre ν β a b Φ := by
    intro c Φ
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    unfold fibre
    rw [← integral_const_mul]
    congr 1
    funext g
    simp only [omA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hzero : fibre ν β a b 0 = 0 := by
    funext x
    simp [fibre, omA]

  let M : Submodule ℂ (GL (Fin (a + b)) k → ℂ) :=
    { carrier := {f | ∃ Ψ ∈ N, Ψ ∈ fullRankSB k a (a + b) ∧ fibre ν β a b Ψ = f}
      zero_mem' := ⟨0, N.zero_mem, (fullRankSB k a (a + b)).zero_mem, hzero⟩
      add_mem' := by
        rintro _ _ ⟨Φ, h1, h2, rfl⟩ ⟨Ψ, h3, h4, rfl⟩
        exact ⟨Φ + Ψ, N.add_mem h1 h3, (fullRankSB k a (a + b)).add_mem h2 h4, hadd Φ h2 Ψ h4⟩
      smul_mem' := by
        rintro c _ ⟨Φ, h1, h2, rfl⟩
        exact ⟨c • Φ, N.smul_mem c h1, (fullRankSB k a (a + b)).smul_mem c h2, hsmul c Φ⟩ }
  have hind : ∀ Ψ ∈ fullRankSB k a (a + b), fibre ν β a b Ψ ∈ indScal ν β a b := by
    intro Ψ hΨ
    refine ⟨?_, Llaw k a b ν β Ψ⟩
    have hle : stabSub ((repA ν β).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin (a + b)) k))) Ψ ≤
        stabSub (rightReg ℂ (GL (Fin (a + b)) k) ℂ) (fibre ν β a b Ψ) := by
      intro h hh
      have hh' : omA ν β 1 h Ψ = Ψ := hh
      show rightReg ℂ (GL (Fin (a + b)) k) ℂ h (fibre ν β a b Ψ) = fibre ν β a b Ψ
      funext x
      show fibre ν β a b Ψ (x * h) = fibre ν β a b Ψ x
      rw [← fibre_omA, hh']
    exact Subgroup.isOpen_mono hle (Lsmooth k a (a + b) ν β hβs Ψ hΨ.1)
  have hMle : M ≤ indScal ν β a b := by
    rintro _ ⟨Ψ, -, hΨ, rfl⟩
    exact hind Ψ hΨ
  have hMst : ∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M := by
    rintro _ ⟨Ψ, h1, h2, rfl⟩ h
    exact ⟨omA ν β 1 h Ψ, hNst h Ψ h1, hS0 h Ψ h2, funext fun x => fibre_omA ν β a b h Ψ x⟩
  rcases Lirr HB k a b ν β hνs hνu hβs hβu M hMle hMst with h0 | hT
  · left
    intro Ψ hΨN hΨr
    have hΨ : Ψ ∈ fullRankSB k a (a + b) := ⟨hNSB hΨN, hΨr⟩
    have hm : fibre ν β a b Ψ ∈ M := ⟨Ψ, hΨN, hΨ, rfl⟩
    rw [h0, Submodule.mem_bot] at hm
    exact Lker k a b ν β hνs hβs Ψ hΨ hm
  · right
    intro Φ hΦ hΦr
    have hΦS : Φ ∈ fullRankSB k a (a + b) := ⟨hΦ, hΦr⟩
    obtain ⟨Ψ, hΨN, hΨS, hZ⟩ := hT (hind Φ hΦS)
    have hd : Φ - Ψ ∈ coinv ν β a (a + b) := by
      refine Lker k a b ν β hνs hβs _ ((fullRankSB k a (a + b)).sub_mem hΦS hΨS) ?_
      rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ, hadd Φ hΦS _ ((fullRankSB k a (a + b)).smul_mem _ hΨS),
        hsmul, hZ]
      simp
    have := N.add_mem (hCN hd) hΨN
    simpa using this

theorem coinv_or_fullRank_le : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) :=
  of_parts _root_.GlobalTheory.RankFibre.indScal_irreducible GlobalTheory.T.fibre_mem_induced_space _root_.GlobalTheory.OmAStab.isOpen_omA_stab GlobalTheory.T.integrable_full_rank_fibre GlobalTheory.T.fibre_zero_mem_coinvariants

end GlobalTheory.RankFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTensorLatticeComponentIntegral
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem piW_smul_incl (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : AF F) (e : E) :
    piW t (a • inclR (F := F) (AF F) e) = evFin F v a * t e := by
  simp [piW, inclR, compFin, TensorProduct.smul_tmul', splitProj_tmul]

theorem comp_mem_splitLat (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (hx : x ∈ L) : (fun i => t (x i)) ∈ splitLat t L := by
  refine ⟨_, tmul_mem_latLoc (one_mem _) hx, funext fun i => ?_⟩
  simp [splitVec, splitProj_tmul]

end GlobalTheory.LatInt

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem map_piW_gen (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : AF F) (x : Fin n → E) (y : Fin d → E) :
    (a • incM F (Matrix.vecMulVec x y)).map (piW t) =
      evFin F v a • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (y j)) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.smul_apply, incM, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [piW_smul_incl, map_mul]

theorem latAtV_comp_integral {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)) (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) :
    ∀ γ ∈ latAtV X W v, ∀ i j,
      ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) i j ∈ v.adicCompletionIntegers F := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, x, hx, y, hy, rfl⟩ := hz
    have hx' := (hb.mem_iff).1 (comp_mem_splitLat v t hx)
    have hy' := (hc.mem_iff).1 (comp_mem_splitLat v t hy)
    intro i j
    rw [map_piW_gen, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    exact mul_mem ha (mul_mem (hx' i) (hy' j))
  | zero => intro i j; simp
  | add γ δ _ _ hγ hδ =>
    intro i j
    rw [Matrix.map_add (piW t) (map_add _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    exact add_mem (hγ i j) (hδ i j)
  | neg γ _ hγ =>
    intro i j
    rw [Matrix.map_neg (piW t) (map_neg _), Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
    exact neg_mem (hγ i j)

end GlobalTheory.LatInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent resG)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.LB (resG_self)
open GlobalTheory.DualPull (appLE_resG resG_appLE)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem sub_mul_sub_eq_zero_of_closure {B : Type*} [CommRing B] (ψ : B →+* B) (s : Set B)
    (hs : Subring.closure s = ⊤) (H : ∀ x ∈ s, ∀ y ∈ s, (x - ψ x) * (y - ψ y) = 0) (x y : B) :
    (x - ψ x) * (y - ψ y) = 0 := by
  have step (x : B) (hx : ∀ y ∈ s, (x - ψ x) * (y - ψ y) = 0) (y : B) :
      (x - ψ x) * (y - ψ y) = 0 := by
    have hy : y ∈ Subring.closure s := hs ▸ Subring.mem_top y
    induction hy using Subring.closure_induction with
    | mem y hy => exact hx y hy
    | zero => simp
    | one => simp
    | add a b _ _ ha hb =>
      calc (x - ψ x) * (a + b - ψ (a + b)) = (x - ψ x) * (a - ψ a) + (x - ψ x) * (b - ψ b) := by
            rw [map_add (f := _)]; ring
        _ = 0 := by rw [ha, hb, add_zero]
    | neg a _ ha =>
      calc (x - ψ x) * (-a - ψ (-a)) = -((x - ψ x) * (a - ψ a)) := by rw [map_neg]; ring
        _ = 0 := by rw [ha, neg_zero]
    | mul a b _ _ ha hb =>
      calc (x - ψ x) * (a * b - ψ (a * b)) =
            b * ((x - ψ x) * (a - ψ a)) + ψ a * ((x - ψ x) * (b - ψ b)) := by rw [map_mul]; ring
        _ = 0 := by rw [ha, hb]; ring
  have hx : x ∈ Subring.closure s := hs ▸ Subring.mem_top x
  revert y
  induction hx using Subring.closure_induction with
  | mem x hx => exact step x (H x hx)
  | zero => intro y; simp
  | one => intro y; simp
  | add a b _ _ ha hb =>
    intro y
    calc (a + b - ψ (a + b)) * (y - ψ y) = (a - ψ a) * (y - ψ y) + (b - ψ b) * (y - ψ y) := by
          rw [map_add (f := _)]; ring
      _ = 0 := by rw [ha, hb, add_zero]
  | neg a _ ha =>
    intro y
    calc (-a - ψ (-a)) * (y - ψ y) = -((a - ψ a) * (y - ψ y)) := by rw [map_neg]; ring
      _ = 0 := by rw [ha, neg_zero]
  | mul a b _ _ ha hb =>
    intro y
    calc (a * b - ψ (a * b)) * (y - ψ y) =
          b * ((a - ψ a) * (y - ψ y)) + ψ a * ((b - ψ b) * (y - ψ y)) := by rw [map_mul]; ring
      _ = 0 := by rw [ha, hb]; ring

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

theorem toTsze_injective : Function.Injective (toTsze O M) :=
  (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt O M))).hom).1

theorem surjective_sec_zeroSec : Function.Surjective (sec (zeroSec O M)) := by
  intro t
  have hs : Function.Surjective (TrivSqZeroExt.fstHom O O M).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have ht : (t : PrimeSpectrum (TrivSqZeroExt O M)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom O O M).toRingHom) := by
    rw [_root_.range_comap_of_surjective _ _ hs]
    intro a ha
    have ha : a.fst = 0 := ha
    have h : a * a = 0 := by ext <;> simp [ha]
    have := (t : PrimeSpectrum (TrivSqZeroExt O M)).isPrime
    exact (this.mem_or_mem (h ▸ Ideal.zero_mem _)).elim id id
  exact ht

theorem kappa_injective : Function.Injective (kappa O M) := by
  letI := (isChart O M).algebra
  letI := topModule O M
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨y, rfl⟩ := ((isChart O M).augCotEquiv (sec_hom _)).surjective x
  obtain ⟨y, rfl⟩ := (RingHom.ker ((isChart O M).aug (sec_hom _))).toCotangent_surjective y
  have h1 : (toTsze O M y).snd = 0 := by
    change (AugCot.lift _ (sndFn O M) (sndFn_der O M)) (((isChart O M).augCotEquiv
      (sec_hom _)).symm ((isChart O M).augCotEquiv (sec_hom _) _)) = 0 at hx
    rw [LinearEquiv.symm_apply_apply, AugCot.lift_toCotangent] at hx
    exact hx
  have h2 : (toTsze O M y).fst = 0 := by
    rw [← toO_sec]
    have : (isChart O M).aug (sec_hom _) y = 0 := y.2
    rw [IsChart.aug_apply] at this
    rw [this, map_zero]
  have h3 : (y : Γ((TM O M).left, ⊤)) = 0 :=
    toTsze_injective O M (by rw [map_zero]; ext <;> simp [h1, h2])
  have : y = 0 := Subtype.ext h3
  rw [this, map_zero, map_zero]

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]


variable (M) in
abbrev preimTop (U : (Sp O).Opens) : (TM O M).left.Opens :=
  (𝟙 (TM O M).left) ⁻¹ᵁ ⊤ ⊓ (TM O M).hom ⁻¹ᵁ U

theorem mul_eq_zero_of_appLE {U : (Sp O).Opens} (hU : IsAffineOpen U)
    (hle : U ≤ sec (zeroSec O M) ⁻¹ᵁ (preimTop M U))
    (a b : Γ((TM O M).left, preimTop M U))
    (ha : (sec (zeroSec O M)).appLE (preimTop M U) U hle a = 0)
    (hb : (sec (zeroSec O M)).appLE (preimTop M U) U hle b = 0) : a * b = 0 := by
  obtain ⟨-, po⟩ := isAffineOpen_and_isPushout (IsPullback.id_horiz (TM O M).hom)
    (isAffineOpen_top (Sp O)) hU (isChart O M).affine (le_top : U ≤ (𝟙 (Sp O)) ⁻¹ᵁ ⊤) le_top
  have hs := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  let ψ := ((TM O M).hom.appLE U (preimTop M U) inf_le_right).hom.comp ((sec (zeroSec O M)).appLE (preimTop M U) U hle).hom
  have hψ₁ (r : Γ(Sp O, U)) : ψ ((TM O M).hom.appLE U (preimTop M U) inf_le_right r) =
      (TM O M).hom.appLE U (preimTop M U) inf_le_right r := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle
      ((TM O M).hom.appLE U (preimTop M U) inf_le_right r)) = _
    rw [appLE_base (sec_hom _) hle inf_le_right le_rfl, resG_self]
  have hψ₂ (x : Γ((TM O M).left, ⊤)) : ψ (Scheme.Hom.appLE (𝟙 (TM O M).left) ⊤ (preimTop M U) inf_le_left x) =
      Scheme.Hom.appLE (𝟙 (TM O M).left) ⊤ (preimTop M U) inf_le_left
        ((TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top x)) := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle
      (resG (TM O M).left (le_top : preimTop M U ≤ ⊤) x)) =
      resG (TM O M).left (le_top : preimTop M U ≤ ⊤) _
    rw [appLE_resG, ← resG_appLE (sec (zeroSec O M)) (le_top : U ≤ ⊤) le_top, appLE_resG]
    exact (resG_appLE (TM O M).hom (le_top : preimTop M U ≤ ⊤) le_top _).symm
  have h₀ (x y : Γ((TM O M).left, ⊤)) :
      (x - (TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top x)) *
        (y - (TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top y)) = 0 := by
    apply toTsze_injective O M
    rw [map_mul, map_sub, map_sub, toTsze_base, toTsze_base, toO_sec, toO_sec, map_zero]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have key := sub_mul_sub_eq_zero_of_closure ψ _ hs (by
    rintro x (⟨x, rfl⟩ | ⟨r, rfl⟩) y (⟨y, rfl⟩ | ⟨s, rfl⟩)
    · rw [hψ₂, hψ₂, ← map_sub, ← map_sub, ← map_mul, h₀, map_zero]
    · rw [hψ₁, sub_self, mul_zero]
    · rw [hψ₁, sub_self, zero_mul]
    · rw [hψ₁, sub_self, zero_mul]) a b
  have ha' : ψ a = 0 := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle a) = 0
    rw [ha, map_zero]
  have hb' : ψ b = 0 := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle b) = 0
    rw [hb, map_zero]
  rwa [ha', hb', sub_zero, sub_zero] at key

variable {A : Over (Sp O)} [GrpObj A]

theorem preimage_le_of_zeroSec (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) {U : (Sp O).Opens}
    {W : A.left.Opens} (hU : U ≤ unitSec A ⁻¹ᵁ W) : (TM O M).hom ⁻¹ᵁ U ≤ z.left ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_zeroSec O M t
  have h₁ : s ∈ (sec (zeroSec O M) ≫ (TM O M).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ := hU h₁
  rw [← show sec (zeroSec O M) ≫ z.left = unitSec A from congrArg (·.left) h] at h₂
  exact h₂

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

theorem eq_of_Phi_eq : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A],
    (GlobalTheory.LieVB.omega A).IsQuasicoherent → (∀ (M : Type) [AddCommGroup M] [Module O M]
      [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A])
      (h' : zeroSec O M ≫ z' = η[A]), (∀ w, Phi z h w = Phi z' h' w) → z = z') := by
  intro O _ A _ hq M _ _ _ _ z z' h h' hΦ
  have hq' : (conormal (sec η[A])).IsQuasicoherent := hq
  have hglob (w : Γ(conormal (sec η[A]), ⊤)) : (cotMap z h).app ⊤ w = (cotMap z' h').app ⊤ w :=
    kappa_injective O M ((Phi_apply z h w).symm.trans ((hΦ w).trans (Phi_apply z' h' w)))
  have : IsIso ((tilde.adjunction (R := .of O)).counit.app (conormal (sec η[A]))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of O) (conormal (sec η[A]))
  have hcot : cotMap z h = cotMap z' h' := by
    apply (GlobalTheory.OmegaGlobal.map_bijective_of_isIso_counit (tilde.adjunction (R := .of O)) _ _).1
    ext s
    exact hglob s
  have hz : sec (zeroSec O M) ≫ z.left = unitSec A := congrArg (·.left) h
  have hz' : sec (zeroSec O M) ≫ z'.left = unitSec A := congrArg (·.left) h'
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun t => ?_)
  obtain ⟨U, W, hU, -, c⟩ := exists_isChart (sec_hom η[A]) (V := ⊤) (x := (TM O M).hom t) trivial
  have hT : IsAffineOpen (preimTop M U) := (isAffineOpen_and_isPushout
    (IsPullback.id_horiz (TM O M).hom) (isAffineOpen_top (Sp O)) c.affine_base (isChart O M).affine
    (le_top : U ≤ (𝟙 (Sp O)) ⁻¹ᵁ ⊤) le_top).1
  have kz : preimTop M U ≤ z.left ⁻¹ᵁ W := inf_le_right.trans (preimage_le_of_zeroSec z h c.le)
  have kz' : preimTop M U ≤ z'.left ⁻¹ᵁ W := inf_le_right.trans (preimage_le_of_zeroSec z' h' c.le)
  have c₀ : IsChart (TM O M).hom (sec (zeroSec O M)) U (preimTop M U) :=
    ⟨c.affine_base, hT, fun x hx => ⟨trivial,
      (le_preimage_iff (π := (TM O M).hom) (sec_hom (zeroSec O M))).2 le_rfl hx⟩, inf_le_right⟩
  have e : z.left.appLE W (preimTop M U) kz = z'.left.appLE W (preimTop M U) kz' := by
    ext f
    rw [← sub_eq_zero]
    have ha : (sec (zeroSec O M)).appLE (preimTop M U) U c₀.le
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 := by
      rw [map_sub, appLE_appLE hz kz c₀.le c.le, appLE_appLE hz' kz' c₀.le c.le, sub_self]
    have hd : d (sec_hom (zeroSec O M)) c₀.le
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 := by
      rw [map_sub, ← cotMap_d z h c.le c₀.le kz f, ← cotMap_d z' h' c.le c₀.le kz' f, hcot,
        sub_self]
    letI := c₀.algebra
    have h₁ : AugCot.d (c₀.aug (sec_hom _))
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 :=
      (c₀.ofAugCot_bijective (sec_hom _)).1 (by rw [c₀.ofAugCot_d, map_zero]; exact hd)
    have h₂ := (AugCot.d_eq_zero_iff _ _).1 h₁
    rw [show c₀.aug (sec_hom _) _ = 0 from ha, map_zero, sub_zero] at h₂
    have hsq : RingHom.ker (c₀.aug (sec_hom (zeroSec O M))) ^ 2 = ⊥ := by
      rw [pow_two, eq_bot_iff, Ideal.mul_le]
      intro a ha' b hb'
      exact (Ideal.mem_bot).2 (mul_eq_zero_of_appLE c.affine_base c₀.le a b ha' hb')
    rw [hsq] at h₂
    exact (Ideal.mem_bot).1 h₂
  refine ⟨preimTop M U, ⟨trivial, hU⟩, ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← c.affine.SpecMap_appLE_fromSpec _ hT kz, ← c.affine.SpecMap_appLE_fromSpec _ hT kz', e]

end GlobalTheory.SqZeroPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

open GlobalTheory.LieVB GlobalTheory.Conormal

theorem kappa_cotMap_cst_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Γ(omega A, ⊤)) :
    kappa O M ((cotMap z h).app ⊤ (cst O c • w)) = c • kappa O M ((cotMap z h).app ⊤ w) := by
  rw [show (cotMap z h).app ⊤ (cst O c • w) = cst O c • (cotMap z h).app ⊤ w from
    (QCoh.appLinear (cotMap z h) ⊤).map_smul (cst O c) w]
  obtain ⟨b, hb⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) ((cotMap z h).app ⊤ w)
  rw [← hb]
  have key : cst O c • d (sec_hom (zeroSec O M)) (isChart O M).le b =
      d (sec_hom (zeroSec O M)) (isChart O M).le ((TM O M).hom.appLE ⊤ ⊤ le_top (cst O c) * b) := by
    rw [d_mul]
    erw [d_base (sec_hom (zeroSec O M)) (isChart O M).le le_top (cst O c)]
    rw [smul_zero, add_zero]
    erw [appLE_base (sec_hom (zeroSec O M)) _ _ le_rfl]
    rfl
  rw [key, kappa_d, kappa_d, map_mul, toTsze_base, TrivSqZeroExt.snd_mul]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem Phi_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A) :
    Phi z h (c • w) = c • Phi z h w :=
  kappa_cotMap_cst_smul O M A z h c w

end GlobalTheory.SqZeroPt
end

