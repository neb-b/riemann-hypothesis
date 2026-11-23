module

public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2.Theta Formalism.L2.DIV Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

def hLat (V : Formalism.BasicNotions.TH.HSp D) (h : Gf V) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  Submodule.span (𝓞 D.host.E)
    (Set.ofPred fun x : Fin V.rank → D.host.E =>
      (Units.val ((h⁻¹ : Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).mulVec
          (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E (L0c D V))

def IsRatMat (V : Formalism.BasicNotions.TH.HSp D) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) : Prop :=
  matHom V (γ : GA D V) = Formalism.UG.bc (incA D) γE

def CoefTie (V : Formalism.BasicNotions.TH.HSp D) (C : CoefDat D V) {S : CSD D.what₂.LL} {J : Subgroup (Gf V)} {χ : J →* ℂˣ}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ J χ) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W)
    (pair : VV D.what₂.LL lam →ₗ⋆[D.what₂.LL] VV D.what₂.LL lam →ₗ[D.what₂.LL] D.what₂.LL)
    (nab del : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) → Submodule (𝓞 D.what₂.LL) (VV D.what₂.LL lam)) : Prop :=
  ∃ e : S.V ≃ₗ[D.what₂.LL] VV D.what₂.LL lam,
    (∀ i j, (bVV D.what₂.LL lam).repr (e (S.bV i)) j ∈ Formalism.DivisionValues.cmMax D.what₂.LL) ∧
    (∀ x, P.coef x = c0 (e x)) ∧
    (∀ x x', pair (e x) (e x') = S.pair x x') ∧
    (∀ c, (S.Nab c).map ((e : S.V →ₗ[D.what₂.LL] VV D.what₂.LL lam).restrictScalars (𝓞 D.what₂.LL)) =
      nab (hLat V (P.y c))) ∧
    (∀ c, (S.Del c).map ((e : S.V →ₗ[D.what₂.LL] VV D.what₂.LL lam).restrictScalars (𝓞 D.what₂.LL)) =
      del (hLat V (P.y c)))

def CoefMapTie (V : Formalism.BasicNotions.TH.HSp D) (C : CoefDat D V) {lam : D.what₂.Tau → DomWeight V.rank}
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W)
    (rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)) : Prop :=
  (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), IsRatMat V γ γE → ∀ v, c0 (rho γE v) = C.ρ γ (c0 v)) ∧
    LinearIndependent ℂ (fun i => c0 (bVV D.what₂.LL lam i)) ∧
    Submodule.span ℂ (Set.range fun i => c0 (bVV D.what₂.LL lam i)) = ⊤

def SplitOff (P : Pl D.host.E) (S : Set (Pl D.host.E)) : Prop :=
  conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal ∧ P ∉ S ∧ ∀ Q ∈ S, Q.asIdeal ≠ conjIdeal (K := D.host.E) P.asIdeal

def IsWtOfPar {N : ℕ} (lam : DomWeight N) (S : Formalism.BasicNotions.TH.SPar) : Prop :=
  S.card = N ∧ ∃ c : Fin N → ℚ, StrictAnti c ∧ (∀ i, ∃ s, (c i, s) ∈ S) ∧ ∀ i, (lam.w i : ℚ) = c i - rhoVec N i

def lamRdef (P : Formalism.BasicNotions.TH.TPar D) (τ : D.what₂.Tau) : DomWeight D.sp.X'.rank :=
  open Classical in
  if h : ∃ lam : DomWeight D.sp.X'.rank, IsWtOfPar lam (P.Dpar D.R.m τ) then h.choose
  else ⟨0, antitone_const⟩

def LamRForced (P : Formalism.BasicNotions.TH.TPar D) : Prop :=
  ∀ τ, IsWtOfPar (lamRdef P τ) (P.Dpar D.R.m τ)

def IsLamPrime {N : ℕ} (lam : DomWeight N) (j : ℕ) (τ : D.what₂.Tau) : Prop :=
  ∃ (hj : 1 ≤ j ∧ j - 1 < D.R.m) (W : Formalism.IndefR.IndefiniteWeightData.WeightData), W.k = D.R.k ∧ W.m = D.R.m ∧ W.t = D.R.t ∧ W.j = j ∧
    (W.e : ℚ) = (D.hc τ).e ⟨j - 1, hj.2⟩ ∧
    (∀ a : Fin (D.R.k - 1), (W.v (a + 2) : ℚ) = (D.hc τ).v a) ∧
    (∀ a : Fin D.R.m, (W.b (a + 1) : ℚ) = (D.hc τ).b a) ∧
    ∀ i : Fin N, (lam.w i : ℚ) = W.lamPrime (i + 1)

def lamLdef (n j : ℕ) (τ : D.what₂.Tau) : DomWeight n :=
  open Classical in
  if h : ∃ lam : DomWeight n, IsLamPrime lam j τ then h.choose else ⟨0, antitone_const⟩

def LamLForced (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ τ : D.what₂.Tau, IsLamPrime (D := D) (lamLdef (D := D) (D.sp.V j).rank j τ) j τ

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

structure FamTie {A : FamIn D.what₂.LL G Pl0 T m} {cR : CoefDat D D.sp.X'} {cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1))}
    {lR : ∀ t, LevEnv D D.sp.X' (A.ok t × ℕ)} {lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)}
    (B : FamReal D A cR cL lR lL)
    (pl : Pl0 → Pl D.host.E) (S : Set (Pl D.host.E)) (Qt : T → Finset (Pl D.host.E))
    (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL))
    (lamR : D.what₂.Tau → DomWeight D.sp.X'.rank)
    (lamL : ∀ (i : Fin m), D.what₂.Tau → DomWeight (D.sp.V ((i : ℕ) + 1)).rank)
    (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL lamR →ₛₗ[D.what₂.embLL] cR.W)
    (c0L : ∀ i : Fin m, VV D.what₂.LL (lamL i) →ₛₗ[D.what₂.embLL] (cL i).W) : Prop where
  ranks : m = D.R.m ∧ A.r = D.R.r ∧ A.t = D.R.t
  v0 : A.v0 = InfinitePlace.mk D.what₂.embLL
  tauL_ok : ∀ τ, D.what₂.embLL.comp (tauL τ) = Formalism.BasicNotions.TH.tauE D τ
  pl_inj : Function.Injective pl
  q : ∀ P, A.q P = Nat.card (kP (pl P))
  S_fin : S.Finite
  ok : ∀ t P, P ∈ A.ok t ↔ SplitOff (pl P) (S ∪ (Qt t : Set (Pl D.host.E)))
  gramR_eq : gramR = D.sp.X'.gram ∨ gramR = -D.sp.X'.gram
  mapR : CoefMapTie D.sp.X' cR c0R (rhoV tauL lamR)
  mapL : ∀ i : Fin m, CoefMapTie (D.sp.V ((i : ℕ) + 1)) (cL i) (c0L i) (rhoVr tauL (lamL i))
  coefR : ∀ t, CoefTie D.sp.X' cR (B.R t).pres lamR c0R (pairV tauL lamR gramR) (nabAt tauL lamR) (delAt tauL lamR)
  coefL : ∀ (i : Fin m) t, CoefTie (D.sp.V ((i : ℕ) + 1)) (cL i) (B.L i t).pres (lamL i) (c0L i)
    (pairVr tauL (lamL i)
      (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram))
    (nabAtr tauL (lamL i)) (delAtr tauL (lamL i))

end Formalism.IndefR.Bridge
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A)

def MIUnit2 (d : X.MIDat fc) : Prop :=
  (∀ e ∈ X.EEl true, d.V e ∈ X.EEl true ∧ ‖d.V e‖ = ‖e‖) ∧
    (∀ u x, fnorm ((fc X.zs).Dc.Xc u Bs.v0) ((d.U u).mulVec x) = fnorm ((fc X.zs).Dc.Xc u Bs.v0) x) ∧
    ((∀ u t, d.ζC u t ≠ 0) ∧ ∀ u w (k : K), Bs.v0.embedding k = d.ζC u (X.μ w) → vw w k = 0) ∧
    ∀ u, d.ζC u Bs.μ0 = 1

def MIstar2 (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) : Prop :=
  ∃ d : X.MIDat fc, X.MIUnit2 d ∧ X.MIid eV sEE d ∧ X.AuNZ d

theorem vw_eq_zero_of_pow {k : K} {n : ℕ} (hn : 0 < n) (hk : k ^ n = 1) (w : HeightOneSpectrum (𝓞 K)) : vw w k = 0 := by
  have h1 : (n : ℤ) * vw w k = 0 := by
    unfold vw
    rw [← FractionalIdeal.count_pow]
    first
    | rw [FractionalIdeal.spanSingleton_pow]
    | rw [← FractionalIdeal.spanSingleton_pow]
    rw [hk, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h (by exact_mod_cast hn.ne')
  · exact h

theorem zetaOK_of_miUnit2 {d : X.MIDat fc} (hU : X.MIUnit2 d) : X.ZetaOK (X.zetaOf d) := by
  refine ⟨fun u => ?_, fun u t => ?_, fun u w => ?_⟩
  · have h : ∃ k : K, Bs.v0.embedding k = d.ζC u Bs.μ0 := ⟨1, by rw [map_one, hU.2.2.2 u]⟩
    apply Bs.v0.embedding.injective
    rw [X.zetaOf_spec u Bs.μ0 h, hU.2.2.2 u, map_one]
  · by_cases h : ∃ k : K, Bs.v0.embedding k = d.ζC u t
    · intro h0
      have h' := X.zetaOf_spec u t h
      rw [h0, map_zero] at h'
      exact hU.2.2.1.1 u t h'.symm
    · rw [X.zetaOf_not u t h]
      exact one_ne_zero
  · by_cases h : ∃ k : K, Bs.v0.embedding k = d.ζC u (X.μ w)
    · exact hU.2.2.1.2 u w _ (X.zetaOf_spec u (X.μ w) h)
    · rw [X.zetaOf_not u (X.μ w) h]
      exact vw_eq_zero_of_pow one_pos (one_pow 1) w

section Ident2

variable {eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH} {d : X.MIDat fc}

theorem embedding_pairing_eq_mul_inner (hW : (fc X.zs).Df1.WF) (hJ : X.JIsoR cv) (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true)
    (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true) (hE : X.EVTie cr cv eV) (hU : X.MIUnit2 d)
    (hI : X.MIid eV sEE d) (u : (fc X.zs).Dc.Mem) (φ : Fin ((fc X.zs).Dc.a u) → K)
    (y : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → K) :
    Bs.v0.embedding (X.Bdef u φ y) =
      d.a u * ⟪sEE (d.V (X.iC cr true Bs.μ0 (cpt Bs.v0.embedding y))),
        (fc X.zs).Sp.Pu u ((d.U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ := by
  have h1 := hI u Bs.μ0 φ ((rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec y)
  rw [hU.2.2.2 u, one_mul, X.theta_eV cr cv eV hJ hRL hDn hUp hC hE] at h1
  have h3 : ((fc X.zs).Df1.Pq Bs.μ0).mulVec ((rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec y) = y :=
    mulVec_rinv _ (hW.Pq_surj Bs.μ0) y
  rw [h3] at h1
  rw [X.iC_cpt' cr true Bs.μ0 y]
  exact h1

theorem zetaC_mul_embedding_Pt (hW : (fc X.zs).Df1.WF) (h2 : X.H2 cr true) (hr : X.RATmu cr true) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (hU : X.MIUnit2 d) (hI : X.MIid eV sEE d) (u : (fc X.zs).Dc.Mem) (t : Bs.Tup)
    (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV t) → K) :
    d.ζC u t * Bs.v0.embedding ((fc X.zs).Dc.Pt u t φ F) =
      Bs.v0.embedding (X.Bdef u φ ((X.rowMat cr true t).mulVec (((fc X.zs).Df1.Pq t).mulVec F))) := by
  rw [X.embedding_pairing_eq_mul_inner cr cv hW hJ hRL hDn hUp hC hE hU hI, hI u t φ F, X.theta_eV cr cv eV hJ hRL hDn hUp hC hE]
  have hx : X.iC cr true Bs.μ0 (cpt Bs.v0.embedding ((X.rowMat cr true t).mulVec (((fc X.zs).Df1.Pq t).mulVec F))) =
      X.Θ t (X.jR t (cr.toR X.zs true t (((fc X.zs).Df1.Pq t).mulVec F))) :=
    (X.key_row cr true h2 hr t _).trans (X.iC_cpt' cr true t _)
  rw [hx]

theorem base_tuple_vanishing_of_hypotheses (hJ : X.JIsoR cv) (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true)
    (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true) (hE : X.EVTie cr cv eV) (hU : X.MIUnit2 d)
    (hI : X.MIid eV sEE d) : X.BtVanish (fc := fc) := by
  intro u φ F hF
  have hP : ((fc X.zs).Df1.Pq Bs.μ0).mulVec F = 0 := LinearMap.mem_ker.1 hF
  have h1 := hI u Bs.μ0 φ F
  have h0 : cr.toR X.zs true Bs.μ0 (((fc X.zs).Df1.Pq Bs.μ0).mulVec F) = 0 := by
    rw [hP]; exact map_zero _
  rw [hU.2.2.2 u, one_mul, X.theta_eV cr cv eV hJ hRL hDn hUp hC hE, h0] at h1
  simp only [map_zero, inner_zero_left, mul_zero] at h1
  exact (map_eq_zero Bs.v0.embedding).1 h1

theorem matrix_identity_of_unit_hypotheses (hW : (fc X.zs).Df1.WF) (h2 : X.H2 cr true) (hr : X.RATmu cr true) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (hU : X.MIUnit2 d) (hI : X.MIid eV sEE d) : X.MatrixIdentityOffBase cr (X.zetaOf d) := by
  intro u t _ φ F
  have hk := X.zetaC_mul_embedding_Pt cr cv hW h2 hr hJ hRL hDn hUp hC hE hU hI u t φ F
  by_cases h : ∃ k : K, Bs.v0.embedding k = d.ζC u t
  · apply Bs.v0.embedding.injective
    rw [map_mul, X.zetaOf_spec u t h, hk]
  · have hP : (fc X.zs).Dc.Pt u t φ F = 0 := by
      by_contra hP
      apply h
      refine ⟨X.Bdef u φ ((X.rowMat cr true t).mulVec (((fc X.zs).Df1.Pq t).mulVec F)) /
        (fc X.zs).Dc.Pt u t φ F, ?_⟩
      rw [map_div₀, ← hk, mul_div_assoc, div_self ((map_ne_zero _).2 hP), mul_one]
    rw [hP, map_zero, mul_zero] at hk
    rw [hP, mul_zero]
    exact ((map_eq_zero _).1 hk.symm).symm

theorem isometric_periods_of_unit_hypotheses (hW : (fc X.zs).Df1.WF) (hpos : X.H4pos) (h2 : X.H2 cr true) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (hS : X.SEEIso sEE) (hU : X.MIUnit2 d) (hI : X.MIid eV sEE d) (hA : X.AuNZ d)
    (ζ : (fc X.zs).Dc.Mem → Bs.Tup → K) : (X.colOf cr (X.colDef ζ sEE)).L1e := by
  have hn : 0 < X.nP true := hpos.2.2 true
  have hli : LinearIndependent ℂ (fun i => X.iC cr true Bs.μ0 (Pi.single i 1)) :=
    li_of_lin_injective (by rw [lin_basis]; exact h2.1)
  have hXE : X.XE cr true Bs.v0 = frameOf (X.gramE cr true) :=
    (rowXE_spec (Df := lv (fc X.zs) true) hW _ (X.gramE_unit cr true h2 hn) X.κ hpos.1
      (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hpos.2.1 j Bs.μ0 p v)).2.1
  have hfn : ∀ y, fnorm (X.XE cr true Bs.v0) y = Real.sqrt (X.nP true)⁻¹ * ‖X.iC cr true Bs.μ0 y‖ := by
    intro y
    rw [hXE, gramE, fnorm_gram_smul _ hli _ (inv_pos.mpr hn), lin_basis]
  have hmem : ∀ y, X.iC cr true Bs.μ0 y ∈ X.EEl true := fun y => h2.2.2 ▸ LinearMap.mem_range_self _ y
  have hsn : ∀ e ∈ X.EEl true, ‖sEE e‖ = Real.sqrt (X.nP true)⁻¹ * ‖e‖ := by
    intro e he
    have h3 : ‖sEE e‖ ^ 2 = (X.nP true)⁻¹ * ‖e‖ ^ 2 := by
      rw [← hS.1 e he, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
    rw [← Real.sqrt_sq (norm_nonneg (sEE e)), h3, Real.sqrt_mul (inv_pos.mpr hn).le, Real.sqrt_sq (norm_nonneg e)]
  have hex : ∀ y, ∃ y', X.iC cr true Bs.μ0 y' = d.V (X.iC cr true Bs.μ0 y) := by
    intro y
    have h4 := (hU.1 _ (hmem y)).1
    rw [← h2.2.2] at h4
    exact LinearMap.mem_range.1 h4
  choose w hw using hex
  let W : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) →ₗ[ℂ] (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) :=
    { toFun := w
      map_add' := fun x y => h2.1 (by simp only [hw, map_add (f := _)])
      map_smul' := fun c y => h2.1 (by simp only [hw, map_smul, RingHom.id_apply]) }
  have hWy : ∀ y, (LinearMap.toMatrix' W).mulVec y = w y := fun y => LinearMap.toMatrix'_mulVec W y
  refine ⟨fun (y : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) => ?_, fun y => ?_, ?_, LinearMap.toMatrix' W,
    fun (y : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) => ?_,
    fun u => ⟨d.a u, hA u, d.U u, hU.2.1 u, fun x (y : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) => ?_⟩⟩
  · exact (hsn _ (hmem y)).trans (hfn y).symm
  · exact hS.2.1 _ (hmem y)
  · show Module.finrank ℂ (fc X.zs).Sp.Rw = (lv (fc X.zs) true).dQ Bs.μ0
    rw [hS.2.2, ← h2.2.2, LinearMap.finrank_range_of_inj h2.1, Module.finrank_fin_fun]
  · have e1 : fnorm (X.XE cr true Bs.v0) ((LinearMap.toMatrix' W).mulVec y) = fnorm (X.XE cr true Bs.v0) (w y) :=
      congrArg _ (hWy y)
    refine e1.trans ((hfn _).trans ?_)
    rw [hw, (hU.1 _ (hmem y)).2]
    exact (hfn y).symm
  · show pairC Bs.v0 (X.Bdef u) x y =
      d.a u * ⟪sEE (X.iC cr true Bs.μ0 ((LinearMap.toMatrix' W).mulVec y)), (fc X.zs).Sp.Pu u ((d.U u).mulVec x)⟫_ℂ
    rw [hWy, hw]
    let Φ : (Fin ((fc X.zs).Dc.a u) → ℂ) →ₗ[ℂ] (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) →ₗ[ℂ] ℂ :=
      LinearMap.mk₂ ℂ
        (fun x y => d.a u * ⟪sEE (d.V (X.iC cr true Bs.μ0 y)), (fc X.zs).Sp.Pu u ((d.U u).mulVec x)⟫_ℂ)
        (fun x x' y => by simp only [Matrix.mulVec_add, map_add (f := _), inner_add_right, mul_add])
        (fun c x y => by simp only [Matrix.mulVec_smul, map_smul, inner_smul_right, smul_eq_mul]; ring)
        (fun x y y' => by simp only [map_add (f := _), inner_add_left, mul_add])
        (fun c x y => by
          simp only [map_smul, LinearMap.map_smulₛₗ, inner_smul_left, smul_eq_mul, starRingEnd_self_apply]; ring)
    have hΦ : d.a u * ⟪sEE (d.V (X.iC cr true Bs.μ0 y)), (fc X.zs).Sp.Pu u ((d.U u).mulVec x)⟫_ℂ = Φ x y := rfl
    rw [hΦ, bil_expand Φ x y, pairC]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have hik : Φ (Pi.single i 1) (Pi.single k 1) = Bs.v0.embedding (X.Bdef u (Pi.single i 1) (Pi.single k 1)) := by
      rw [X.embedding_pairing_eq_mul_inner cr cv hW hJ hRL hDn hUp hC hE hU hI, cpt_single, cpt_single]
      rfl
    rw [hik]

end Ident2

theorem btVanish_of_miStar2 (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (hW : (fc X.zs).Df1.WF) (hpos : X.H4pos) (h2 : X.H2 cr true) (hr : X.RATmu cr true) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (hS : X.SEEIso sEE) (hM : X.MIstar2 eV sEE) :
    X.BtVanish (fc := fc) ∧ ∃ ζ : (fc X.zs).Dc.Mem → Bs.Tup → K, X.MatrixIdentityOffBase cr ζ ∧ X.ZetaOK ζ ∧
      (X.colOf cr (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e := by
  obtain ⟨d, hU, hI, hA⟩ := hM
  exact ⟨X.base_tuple_vanishing_of_hypotheses cr cv hJ hRL hDn hUp hC hE hU hI, X.zetaOf d,
    X.matrix_identity_of_unit_hypotheses cr cv hW h2 hr hJ hRL hDn hUp hC hE hU hI, X.zetaOK_of_miUnit2 hU,
    X.isometric_periods_of_unit_hypotheses cr cv hW hpos h2 hJ hRL hDn hUp hC hE hS hU hI hA _⟩

theorem exists_zeta_pairing_factors_through_periods (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (hW : (fc X.zs).Df1.WF) (hpos : X.H4pos) (h2 : X.H2 cr true) (hr : X.RATmu cr true) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (hS : X.SEEIso sEE) (hM : X.MIstar2 eV sEE) :
    ∃ ζ : (fc X.zs).Dc.Mem → Bs.Tup → K, (X.colOf cr (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).PairingFactorsThroughPeriods ∧
      (X.colOf cr (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e := by
  obtain ⟨hBt, ζ, hMI, hZ, hL⟩ := X.btVanish_of_miStar2 cr cv eV sEE hW hpos h2 hr hJ hRL hDn hUp hC hE hS hM
  exact ⟨ζ, X.cutPairing cr ζ sEE hW h2 hBt hMI hZ, hL⟩

end CxData

end Formalism.IndefR.Cx
end
end

