module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDefs
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecompositionOfThreeParts
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundReal
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ExistsMapOfCoefGe
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Model

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] (K : ℕ) {J : ℕ} (nL : ZMod J → ℕ)

def mlPos : ML J nL r → ZMod J × ℤ
  | ML.ll j l => (j, llPos Fr (segZ j) l.val)
  | ML.lab j m => (j, Fr.fr (segZ j) (r - 1 - m.val))
  | ML.wc j m => (j + 1, Fr.fr (segZ (j + 1) - 1) (r - 1 - m.val))
  | ML.tp j m _ => (j, Fr.fr (segZ j) (r - 1 - m.val))

def tlPos (x : TL J nL r) : ZMod J × ℤ := (x.1, posTL Fr x)

def LSeg (J : ℕ) : Letters (ZMod J × ℤ) := ⟨fun x => decide (Even x.2)⟩

def xiPl (Go : MvPolynomial (ML J nL r × Fin r) O) : MvPolynomial ((ZMod J × ℤ) × Fin r) O :=
  rename (fun v => (mlPos Fr nL v.1, v.2)) Go

def xiNo (No : MvPolynomial (TL J nL r × Fin K) O) : MvPolynomial ((ZMod J × ℤ) × Fin K) O :=
  rename (fun v => (tlPos Fr nL v.1, v.2)) No

def PhiPl (J : ℕ) : MvPolynomial ((ZMod J × ℤ) × Fin r) O →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => X (posOf n' v.1.2, Fin.castAdd K v.2) ^ (p ^ Fr.dist (segZ v.1.1) v.1.2)

def PhiNo (J : ℕ) : MvPolynomial ((ZMod J × ℤ) × Fin K) O →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => X (posOf n' v.1.2, Fin.natAdd r v.2) ^ (p ^ Fr.dist (segZ v.1.1) v.1.2)

def labO [NeZero J] (rho : TL J nL r × Fin (r + K) → ℕ) : Fin n' × Fin (r + K) →₀ ℕ :=
  ∑ x : TL J nL r, ∑ c : Fin (r + K), Finsupp.single (posOf n' (posTL Fr x), c) (rho (x, c))

end Model

def toKK {O : Type} [CommRing O] [IsDomain O] {n' m r K : ℕ} (hk : m + 1 = r + K) (P : RRing O n' (r + K)) :
    MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O)) (rename (castVK hk) P)

structure MFH (p : ℕ) {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (TT : Finset (Fin n')) (L₁ L₂ N₁ G' : ℕ)
    (deg d : Fin n' → ℕ) (Y : ℝ) (k cP : ℕ) : Prop where
  prime : p.Prime
  two_le_r : 2 ≤ r
  frames : FramesOK TT L₁ L₂ N₁ G' Fr
  d_top : ∀ s ∈ Fr.TT, d s = deg s
  d_off : ∀ s, s ∉ Fr.TT → d s = 0
  margin : ∀ j x : ℤ, x ∈ Fr.letters j → ¬ Fr.IsW j x → 128 * (cP : ℝ) ≤ (sl p Fr deg Y k j x : ℝ)

section At

variable (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  (d : Fin n' → ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ)
  (ka : ZMod J → ℕ → Fin K → ℤ) (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
  (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)

def MH : Prop :=
  SignedChainDegreeCondition p O Fr deg Y N₁ G' cP Dt dPl ka ∧ BlockOK Fr p Dt.nL d rho dPl dNo ∧
  NormTest p O cP Dt dNo ka (MvPolynomial.map (algebraMap O (KK O)) No) ∧
  Dt.YY 24 60 (MvPolynomial.map (algebraMap O (KK O)) Go) ∧
  ∀ mo ∈ Go.support, Dt.ph (monomial mo 1) ∈ Pol (KK O) r Dt.d

def Occ (δ : ZMod J × ℤ → ℕ) : Prop := ∃ mo ∈ (xiPl Fr O Dt.nL Go).support, ∀ i, multideg mo i = δ i

def DecAt : Prop :=
  ∀ δ : ZMod J × ℤ → ℕ, Occ p O Fr Dt Go δ →
    ∃ (n : ℕ) (obd : ℤ → ℤ → ℝ) (xi : Fin n → ℤ → SegRing O r K) (dd : ℤ → ℤ → ℕ),
      (∀ (i : Fin n) (j : ℕ), j < Fr.J →
        xi i j ∈ XX' O r K Fr j (fun _ => (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ))
          (fun x => Bo p Fr deg j x / 2 - sl p Fr deg Y (r + K) j x) (obd j) ∧
        xi i j ∈ restrictSupport O {mm | ∀ x ∈ Fr.letters j, ∑ c : Fin (r + K), mm (x, c) = dd j x}) ∧
      (∀ j : ℕ, j < Fr.J → ∀ x ∈ Fr.letters j, (Fr.IsW j x ∨ x ∈ Fr.LLset j) →
        (dd j x : ℝ) ≤ levDeg p Fr deg j x + levDeg p Fr deg j x / 100) ∧
      ∑ i, ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (xi i j) =
        PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No)

def AlgAt : Prop :=
  toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))) =
    asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
      (MvPolynomial.map (algebraMap O (KK O)) No)

def DegAt : Prop :=
  ∀ δ : ZMod J × ℤ → ℕ, Occ p O Fr Dt Go δ →
    HasMultideg (toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No)))) d ∧
    ∃ o : ℕ, ∀ mm ∈ (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))).support,
      normDeg r mm = o

def LabAt : Prop :=
  IsLabel p Fr (labO Fr K Dt.nL rho) ∧ ∀ v ∈ (labO Fr K Dt.nL rho).support, v.1 ∈ Fr.TT

end At

theorem sum_homComp {R : Type} [CommRing R] {ι : Type} {n : ℕ} (F : MvPolynomial (ι × Fin n) R) :
    ∑ δ ∈ F.support.image (fun mo => fun i => multideg mo i), homComp δ F = F := by
  classical
  conv_rhs => rw [F.as_sum]
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (s := F.support)
    (t := F.support.image (fun mo => fun i => multideg mo i)) (g := fun mo => fun i => multideg mo i)
    (fun mo hmo => Finset.mem_image_of_mem _ hmo)]
  apply Finset.sum_congr rfl
  intro δ _
  unfold homComp
  apply Finset.sum_congr
  · ext mo
    simp only [Finset.mem_filter, funext_iff]
  · intro _ _
    rfl

private theorem mem_range_algebraMap_of_vK_nonneg {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (x : KK O) (h : geQ (vK p x) 0) : x ∈ Set.range (algebraMap O (KK O)) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero]⟩
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) x
  have hb : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hbK : algebraMap O (KK O) (b : O) ≠ 0 :=
    fun h0 => hb ((IsFractionRing.injective O (KK O)) (h0.trans (map_zero _).symm))
  have ha : a ≠ 0 := by
    intro ha0
    apply hx
    rw [ha0, map_zero] at hab
    exact (mul_eq_zero.mp hab).resolve_right hbK
  have hord := Formalism.MainNotions.G.Joints.ordW_eq x a b ha hb hab
  have hp0 : IsDiscreteValuationRing.addVal O (p : O) ≠ 0 := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mp S.p_mem
  have hpt : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact S.p_ne
  have hram : 0 < ramE p O := by
    unfold ramE
    rcases ENat.ne_top_iff_exists.mp hpt with ⟨k, hk⟩
    rw [← hk] at hp0 ⊢
    simp only [ENat.toNat_coe]
    exact Nat.pos_of_ne_zero (by exact_mod_cast hp0)
  have hq := h ((((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) / (ramE p O : ℚ))
    (by rw [vK, hord, WithTop.map_coe])
  have hq' : (0 : ℚ) ≤ (((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) /
      (ramE p O : ℚ) := by exact_mod_cast hq
  have hd : (0 : ℚ) < ramE p O := by exact_mod_cast hram
  have hnum : (0 : ℚ) ≤ (((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) :=
    (div_nonneg_iff.mp hq').elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hd))
  have hle : Formalism.MainNotions.G.Joints.nv (b : O) ≤ Formalism.MainNotions.G.Joints.nv a := by
    have : (0 : ℤ) ≤ (Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) := by exact_mod_cast hnum
    omega
  have hat : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact ha
  have hbt : IsDiscreteValuationRing.addVal O (b : O) ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hb
  have hvle : IsDiscreteValuationRing.addVal O (b : O) ≤ IsDiscreteValuationRing.addVal O a := by
    rw [← ENat.coe_toNat hat, ← ENat.coe_toNat hbt]
    exact_mod_cast hle
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.mp hvle
  refine ⟨c, ?_⟩
  rw [hc, map_mul] at hab
  exact (mul_left_cancel₀ hbK (by rw [← hab, mul_comm])).symm

theorem exists_map_of_coefGe {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) {σ : Type} (F : MvPolynomial σ (KK O)) (h : CoefGe p F 0) :
    ∃ Fo : MvPolynomial σ O, MvPolynomial.map (algebraMap O (KK O)) Fo = F := by
  have hrange : F ∈ Set.range (MvPolynomial.map (algebraMap O (KK O))) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro x hx
    obtain ⟨mo, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hx
    exact mem_range_algebraMap_of_vK_nonneg S _ (h mo)
  obtain ⟨Fo, hFo⟩ := hrange
  exact ⟨Fo, hFo⟩

theorem support_of_map {O : Type} [CommRing O] [IsDomain O] {σ : Type} (Fo : MvPolynomial σ O) :
    (MvPolynomial.map (algebraMap O (KK O)) Fo).support = Fo.support := by
  exact MvPolynomial.support_map_of_injective _ (IsFractionRing.injective O (KK O))

theorem membAt_core (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
    (d : Fin n' → ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J)
    (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
    (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)
    (hDec : DecAt p O Fr deg Y N₁ G' cP Dt No Go) (hAlg : AlgAt p O hk Fr Dt rho No Go)
    (hDeg : DegAt p O hk Fr d Dt rho No Go) (hLab : LabAt p O Fr Dt rho) :
    ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
      (∀ q, HasMultideg (sig q) d ∧ OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk (o q) (sig q)) ∧
      ∑ q, sig q = asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
        (MvPolynomial.map (algebraMap O (KK O)) No) := by
  classical
  set S := (xiPl Fr O Dt.nL Go).support.image (fun mo => fun i => multideg mo i) with hS
  have hocc : ∀ δ ∈ S, Occ p O Fr Dt Go δ := by
    intro δ hδ
    obtain ⟨mo, hmo, rfl⟩ := Finset.mem_image.mp hδ
    exact ⟨mo, hmo, fun i => rfl⟩
  let e := S.equivFin
  let δq : Fin S.card → (ZMod J × ℤ → ℕ) := fun q => ((e.symm q : S) : ZMod J × ℤ → ℕ)
  let G : (ZMod J × ℤ → ℕ) → MvPolynomial (Fin n' × Fin (r + K)) O := fun δ =>
    monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))
  have hoc : ∀ q, Occ p O Fr Dt Go (δq q) := fun q => hocc _ (e.symm q).2
  choose o ho using fun q => (hDeg (δq q) (hoc q)).2
  refine ⟨S.card, o, fun q => toKK hk (G (δq q)), fun q => ⟨(hDeg (δq q) (hoc q)).1, ?_⟩, ?_⟩
  · obtain ⟨n, obd, xi, dd, h1, h2, h3⟩ := hDec (δq q) (hoc q)
    have hmon : monPh O K p Fr (labO Fr K Dt.nL rho) xi = G (δq q) := by
      simp only [monPh, G, h3]
    refine ⟨n, obd, xi, dd, labO Fr K Dt.nL rho, h1, h2, hLab.1, hLab.2, ?_, ?_⟩
    · rw [hmon]
      exact ho q
    · rw [hmon]
      rfl
  · have hAlg' : toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
        (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))) =
        asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
          (MvPolynomial.map (algebraMap O (KK O)) No) := hAlg
    rw [← hAlg']
    have hsum : ∑ q, toKK hk (G (δq q)) = ∑ δ ∈ S, toKK hk (G δ) := by
      rw [Equiv.sum_comp e.symm (fun x : S => toKK hk (G x)), Finset.sum_coe_sort S (fun δ => toKK hk (G δ))]
    rw [hsum]
    have e2 : ∑ δ ∈ S, toKK hk (G δ) = toKK hk (∑ δ ∈ S, G δ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [toKK, map_sum]
    rw [e2]
    congr 1
    simp only [G]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.mul_sum, ← Finset.sum_mul, ← map_sum, hS, sum_homComp]

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickDefs
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def gamR (P rho be : ℕ) : ℚ :=
  ((rho + P * be).factorial : ℚ) / ((rho.factorial : ℚ) * (be.factorial : ℚ) * (P.factorial : ℚ) ^ be)

def diagK {Kf : Type} [Field Kf] {σ : Type} (g : (σ →₀ ℕ) → Kf) (F : MvPolynomial σ Kf) : MvPolynomial σ Kf :=
  ∑ mo ∈ F.support, monomial mo (g mo * F.coeff mo)

section Dig

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

def gamPl (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) : ℚ :=
  ∏ v : TL J nL r × Fin r, gamR (lowP Fr p v.1) (rho (v.1, Fin.castAdd K v.2)) (bp v)

def gamNo (rho : TL J nL r × Fin (r + K) → ℕ) (bn : TL J nL r × Fin K →₀ ℕ) : ℚ :=
  ∏ v : TL J nL r × Fin K, gamR (lowP Fr p v.1) (rho (v.1, Fin.natAdd r v.2)) (bn v)

def cstOf (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) : ℕ :=
  (∏ v : TL J nL r × Fin (r + K), (rho v).factorial) * ∏ x : TL J nL r, (lowP Fr p x).factorial ^ (dPl x + dNo x)

def classOf (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r × Fin (r + K) → ℕ :=
  fun v => Fin.addCases (fun a => mo (plVar Fr hk nL v.1 a) % lowP Fr p v.1)
    (fun b => mo (noVar Fr hk nL v.1 b) % lowP Fr p v.1) v.2

def blkPl (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r → ℕ := fun x => ∑ a : Fin r, mo (plVar Fr hk nL x a) / lowP Fr p x

def blkNo (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r → ℕ := fun x => ∑ b : Fin K, mo (noVar Fr hk nL x b) / lowP Fr p x

def DigFacts (d : Fin n' → ℕ) : Prop :=
  ∀ G : MvPolynomial (TV n' (m + 1)) (KK O), HasMultideg G d →
    (∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ), (∀ x c, rho (x, c) < lowP Fr p x) →
      ∀ A ∈ Pol (KK O) r dPl, ∀ N ∈ Pol (KK O) K dNo,
        fock G (asm Fr p O hk nL rho A N) = ((cstOf Fr p nL rho dPl dNo : ℕ) : KK O) *
          ∑ bp ∈ A.support, ∑ bn ∈ N.support, ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn *
            (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
            (((gamNo Fr p nL rho bn : ℚ) : KK O) * N.coeff bn * ((expFact bn : ℕ) : KK O))) ∧
    (∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (bp : TL J nL r × Fin r →₀ ℕ),
      (levImg Fr p hk nL rho dPl dNo G).coeff bp ∈ Pol (KK O) K dNo) ∧
    ∀ mo ∈ G.support,
      BlockOK Fr p nL d (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) ∧
      ((levImg Fr p hk nL (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) G).coeff
        (plMon Fr p hk nL mo)).coeff (noMon Fr p hk nL mo) = G.coeff mo ∧
      (∀ x, multideg (plMon Fr p hk nL mo) x = blkPl Fr p hk nL mo x) ∧
      (∀ x, multideg (noMon Fr p hk nL mo) x = blkNo Fr p hk nL mo x) ∧
      ((expFact mo : ℕ) : ℚ) = ((cstOf Fr p nL (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) : ℕ) : ℚ) *
        ((expFact (plMon Fr p hk nL mo) : ℕ) : ℚ) * ((expFact (noMon Fr p hk nL mo) : ℕ) : ℚ) *
        gamPl Fr p nL (classOf Fr p hk nL mo) (plMon Fr p hk nL mo) *
        gamNo Fr p nL (classOf Fr p hk nL mo) (noMon Fr p hk nL mo)

end Dig

section Parts

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) {J : ℕ} [NeZero J]

def DnoOf (nL : ZMod J → ℕ) (dNo : TL J nL r → ℕ) : ℕ :=
  ∑ i : Σ j : ZMod J, Fin (nL j + r + 1), N0 K * Nat.log p (2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1)

def JPOK (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
    (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))) : Prop :=
  IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e ∧
  (∀ F G, fock (e F) G = fock F (e G)) ∧
  (∀ F ∈ Pol (KK O) K dNo, e F ∈ Pol (KK O) K dNo ∧
    (InBB (O := O) p F → InBB (O := O) p (((p : KK O) ^ DnoOf (K := K) p Dt.nL dNo) • e F))) ∧
  ∀ F i, e F ∈ isoSub (normE p K Dt i) (ka i.1 i.2.val)

def JPAt (Dt : SignedChainData p O r J) : Prop :=
  ∀ (dNo : TL J Dt.nL r → ℕ), ∀ y ∈ Pol (KK O) K dNo,
    ∃ (ka : ZMod J → ℕ → Fin K → ℤ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      JPOK p O Dt dNo ka e ∧ vBB (O := O) p (e y) ≤ vBB (O := O) p y

def NoAt (cP : ℕ) (Dt : SignedChainData p O r J) : Prop :=
  ∀ (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ) (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
    (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))) (nu : TL J Dt.nL r × Fin K →₀ ℕ),
    (∀ x c, rho (x, c) < lowP Fr p x) → JPOK p O Dt dNo ka e → (∀ x, multideg nu x = dNo x) →
    ∃ (N0 : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) (cY : KK O),
      NormTest p O cP Dt dNo ka N0 ∧
      leQ (vK p cY) ((padicValNat p (∏ x, (dNo x).factorial) : ℝ) / 2 + DnoOf (K := K) p Dt.nL dNo -
        (padicValNat p (expFact nu) : ℝ) / 2) ∧
      CoefGe p (N0 - diagK (fun bn => ((gamNo Fr p Dt.nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1))) cP

def GaAt (nL : ZMod J → ℕ) : Prop :=
  ∀ rho : TL J nL r × Fin (r + K) → ℕ, (∀ x c, rho (x, c) < lowP Fr p x) →
    (∀ bn : TL J nL r × Fin K →₀ ℕ, gamNo Fr p nL rho bn ≠ 0 ∧ padicValRat p (gamNo Fr p nL rho bn) = 0) ∧
    (∀ bp : TL J nL r × Fin r →₀ ℕ, gamPl Fr p nL rho bp ≠ 0 ∧ padicValRat p (gamPl Fr p nL rho bp) = 0) ∧
    ∃ ga : (TL J nL r × Fin r →₀ ℕ) → O, (∀ al, IsUnit (ga al)) ∧
      (∀ al, algebraMap O (KK O) (ga al) = ((gamPl Fr p nL rho al : ℚ) : KK O)) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ ε : Bool, ∃ lam : (TL J nL r × Fin r →₀ ℕ) →₀ O,
        (∀ m ∈ lam.support, (m.sum fun _ e => e) ≤ 6 * k) ∧
        ∀ al : TL J nL r × Fin r →₀ ℕ,
          geQ (vK p ((if ε then algebraMap O (KK O) (ga al) else (algebraMap O (KK O) (ga al))⁻¹) -
            binomCombF (K := KK O) lam al)) (k : ℝ)

def SizeAt (nL : ZMod J → ℕ) (d : Fin n' → ℕ) (Dn : ℝ) : Prop :=
  ∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ), BlockOK Fr p nL d rho dPl dNo →
    ∀ (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ),
      (∀ x, multideg bp x = dPl x) → (∀ x, multideg bn x = dNo x) →
      (DnoOf (K := K) p nL dNo : ℝ) +
        ((padicValNat p (∏ x, (dPl x).factorial) : ℝ) - (padicValNat p (expFact bp) : ℝ)) / 2 +
        ((padicValNat p (∏ x, (dNo x).factorial) : ℝ) - (padicValNat p (expFact bn) : ℝ)) / 2 ≤ Dn

end Parts

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosTLSurj
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] {nL : ZMod J → ℕ}

theorem llPos_surj (j y : ℤ) (hy : y ∈ Fr.LLset j) : ∃ l, l < (Fr.LLset j).card ∧ llPos Fr j l = y := by
  have hm : y ∈ (Fr.LLset j).sort (· ≤ ·) := (Finset.mem_sort _).mpr hy
  obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i, by rwa [Finset.length_sort] at hi, ?_⟩
  unfold Formalism.MainNotions.TestSideWords.llPos
  rw [List.getD_eq_getElem _ _ hi, hiy]

theorem posTL_surj (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card)
    (s : Fin n') (hs : s ∈ Fr.TT) : ∃ x : TL J nL r, posOf n' (posTL Fr x) = s := by
  have hper : Fr.fr ((Fr.J : ℤ) - 1) (r - 1) = Fr.fr (-1) (r - 1) + n' := by
    have := hV.2.1 (-1) (r - 1)
    rw [← this]; congr 1
  set c : ℤ := Fr.fr (-1) (r - 1) + 1 with hc
  have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have b1 := Int.emod_nonneg ((s.val : ℤ) - c) hn0.ne'
  have b2 := Int.emod_lt_of_pos ((s.val : ℤ) - c) hn0
  have b3 := Int.emod_def ((s.val : ℤ) - c) n'
  have hx0 : c + ((s.val : ℤ) - c) % n' = (s.val : ℤ) + n' * (-(((s.val : ℤ) - c) / n')) := by
    rw [b3]; ring
  have hp : posOf n' (c + ((s.val : ℤ) - c) % n') = s := by
    rw [hx0, posOf_add_mul_alt, posOf_natCast_self]
  set y : ℤ := c + ((s.val : ℤ) - c) % n' with hy
  have hyT : posOf n' y ∈ Fr.TT := by rw [hp]; exact hs
  obtain ⟨j, h1, h2⟩ := mn_cover Fr L₁ N₁ hV hr y hyT
  have h3 : y ∈ nonW Fr j := by
    unfold nonW; rw [Finset.mem_filter]; exact ⟨h1, h2⟩
  have h4 := (ph_mem_nonW Fr hV hr _ _).1 h3
  have j0 : 0 ≤ j := by
    by_contra h
    have := ph_z_mono Fr hV hr (j := j) (j' := -1) (by omega)
    omega
  have j1 : j < Fr.J := by
    by_contra h
    have := ph_z_mono Fr hV hr (j := (Fr.J : ℤ) - 1) (j' := j - 1) (by omega)
    omega
  set jj : ZMod J := (j.toNat : ZMod J) with hjj
  have hseg : segZ jj = j := by
    unfold segZ
    rw [hjj, ZMod.val_natCast_of_lt (by rw [hJ]; omega)]
    omega
  rcases lt_or_ge y (Fr.fr j 0) with hlt | hge
  · have hyL : y ∈ Fr.LLset (segZ jj) := by
      rw [hseg]
      exact (mem_LLset Fr _ _).2 ⟨⟨h4.1, hlt⟩, hyT⟩
    obtain ⟨l, hl, he⟩ := llPos_surj Fr _ _ hyL
    refine ⟨⟨jj, Sum.inl ⟨l, by rw [hnL]; exact hl⟩⟩, ?_⟩
    show posOf n' (llPos Fr (segZ jj) l) = s
    rw [he]; exact hp
  · obtain ⟨i, hi, he⟩ := ge_frame Fr L₁ N₁ hV j y hyT hge (r - 1) (by omega) h4.2.1
    refine ⟨⟨jj, Sum.inr ⟨r - 1 - i, by omega⟩⟩, ?_⟩
    show posOf n' (Fr.fr (segZ jj) (r - 1 - (r - 1 - i))) = s
    have e : r - 1 - (r - 1 - i) = i := by omega
    rw [e, hseg, ← he]; exact hp

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ValLamOfSubset
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G

section Z

variable {B : Type*} [CommRing B] {σ τ : Type*}

def FinalFormK (k : ℤ) (H : MvPolynomial σ (LaurentPolynomial B)) : Prop := ∀ m, (H.coeff m).coeff k = 0

end Z

section S

variable {R : Type*} [CommRing R] {ι : Type*} {n : ℕ}

theorem notMem_sDegs_iff (LL : Letters ι) (S : Set ι) (j : Fin n) (G : MvPolynomial (ι × Fin n) R) (k : ℤ) :
    k ∉ sDegs LL S j G ↔ FinalFormK k (twistSub LL S j G) := by
  unfold sDegs FinalFormK
  rw [Finset.mem_biUnion]
  constructor
  · intro h m
    by_contra hm
    apply h
    refine ⟨m, ?_, Finsupp.mem_support_iff.2 hm⟩
    rw [mem_support_iff]
    intro h0
    rw [h0] at hm
    simp at hm
  · rintro h ⟨m, _, hm⟩
    exact (Finsupp.mem_support_iff.1 hm) (h m)

theorem sDegs_subset_of {ι' : Type*} (LL : Letters ι) (S : Set ι) (LL' : Letters ι') (S' : Set ι') (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R) (F : MvPolynomial (ι' × Fin n) R)
    (h : ∀ k, FinalFormK k (twistSub LL' S' j F) → FinalFormK k (twistSub LL S j G)) : sDegs LL S j G ⊆ sDegs LL' S' j F := by
  intro k hk
  by_contra hk'
  exact ((notMem_sDegs_iff LL S j G k).2 (h k ((notMem_sDegs_iff LL' S' j F k).1 hk'))) hk

theorem val_lam_of_subset [NeZero n] {ι' : Type*} (LL : Letters ι) (S : Set ι) (LL' : Letters ι') (S' : Set ι')
    (G : MvPolynomial (ι × Fin n) R) (F : MvPolynomial (ι' × Fin n) R)
    (h : ∀ j, sDegs LL S j G ⊆ sDegs LL' S' j F) :
    valS LL' S' F ≤ valS LL S G ∧ lam1S LL S G ≤ lam1S LL' S' F :=
  ⟨Finset.inf_mono (h _), Finset.sup_mono (h _)⟩

end S

end Formalism.MainNotions.Proposition5Numerics
end
end

