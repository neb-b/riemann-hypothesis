module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInJAlt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ToBSurj
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatFinal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0276
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0278
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0268
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0270
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0280
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0271
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompatAlt
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg Pb

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

structure RhoEx : Prop where
  ex : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), M.Sm → ∀ r j : ℕ, r < m → ∀ x : Y.Fam M r j, CB.Comp x → ∃! w, L.Rho x w
  add : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) (x y : Y.Fam M r j) w w', L.Rho x w → L.Rho y w' → L.Rho (x + y) (w + w')
  smul : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) (c : Y.Λ) (x : Y.Fam M r j) w, L.Rho x w →
    L.Rho (c • x) (L.ι (L.lam c) • w)

def CoEx : Prop := ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), M.Sm → ∀ r j : ℕ, r < m →
  Spans L.γB M.q (L.QB M) L.tB_mem r j ∧ ∃ co, IsCo L.γB M.q (L.QB M) L.θ L.tB_mem r j co

def HomRho : Prop := ∀ {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
  {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K}
  (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (mm : ∀ n, GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (sn n)),
  (∀ (n : ℕ) (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), ((mm n).pt.app B₀ y).1.2 = (show Spec B₀ ⟶ M.X from y.1.2) ≫ u) →
  ∀ (r j : ℕ) (x : Y.Fam N r j) (w : HG (L.QB N) r j), L.Rho x w →
    L'.Rho (M := M) (fun n => (pdOm (mm n) sΛ (h.cris n) r).pull j (x n)) (h.fW u hu r j w)

def HomMu : Prop := ∀ {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
  {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K}
  (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (a r j : ℕ) (y : Hdg N.q a j),
    h.fW u hu r j (L.μ N a r j y) = h.cB ^ (r - a) • L'.μ M a r j (pullH (Model.genMap u hu) (Model.genMap_q u hu) a j y)

structure MulRho : Prop where
  sh : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) w, L.Rho x w →
    L.Rho (CB.shS k h x) (shG (L.QB M) L.tB_mem k h j w)
  sh_μ : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' j : ℕ} (k : ℕ) (h : r + k = r') (a : ℕ), a ≤ r → ∀ y : Hdg M.q a j,
    shG (L.QB M) L.tB_mem k h j (L.μ M a r j y) = L.μ M a r' j y
  cup : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) w w',
    L.Rho x w → L.Rho y w' → L.Rho (CB.cupS h x y) (cupG (L.QB M) h w w')
  cup_μ : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' s i j a a' c : ℕ} (h : r + r' = s) (ha : a + a' = c), a ≤ r → a' ≤ r' →
    ∀ (y : Hdg M.q a i) (y' : Hdg M.q a' j),
    cupG (L.QB M) h (L.μ M a r i y) (L.μ M a' r' j y') = L.μ M c s (i + j) (cupH M.q ha rfl y y')
  one : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), L.Rho (Y.oneS M) (L.μ M 0 0 0 (oneH M.q))

def FirstChernHodgeTateCompat : Prop := ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), 1 < m → ∀ (D : E.LineData M.X), sSup (𝒱D D) = ⊤ →
  ∀ (x : Y.Fam M 1 2) (c : Hdg M.q 1 2), CB.IsFirstChernClassInFamily D x → IsDlogFirstChernClass M.q (genD D) c → L.Rho x (L.μ M 1 1 2 c)

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.GaloisTTransform
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dividedPowerFiltration_one {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) : pdP δ 1 = J := by
  refine le_antisymm (Ideal.span_le.2 ?_) fun z hz => by simpa using pow_mem_pdP δ hz 1
  rintro _ ⟨L, hL, hr, rfl⟩
  induction L with
  | nil => simp at hr
  | cons q L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons] at hr ⊢
    rcases Nat.eq_zero_or_pos q.1 with h | h
    · exact J.mul_mem_left _ (ih (fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')) (by omega))
    · exact J.mul_mem_right _ (δ.dpow_mem h.ne' (hL q List.mem_cons_self))

structure Br (R : Per l K) (Y : CB l K) (e : Y.Λ →+* R.A) (θP : R.P →+* ℂ_[l]) (sΛ : K.fixingSubgroup → Y.Λ →+* Y.Λ)
    (sn : K.fixingSubgroup → ∀ n, Y.R n →+* Y.R n) (sC : K.fixingSubgroup → ℂ_[l] →+* ℂ_[l]) (c : K.fixingSubgroup → ℂ_[l]) : Prop where
  et : e Y.t = R.t
  t_ne : R.tB ≠ 0
  θ_i : ∀ x, ∃ y : R.P, (y : R.B) = R.i (e x) ∧ θP y = Y.θ x
  θ_o : ∀ k : K, ∃ y : R.P, (y : R.B) = R.o k ∧ θP y = kC K k
  ker : ∀ x : R.P, θP x = 0 ↔ ∃ y : R.P, (x : R.B) = R.tB * y
  θ_σ : ∀ (g : K.fixingSubgroup) (x : R.P), ∃ y : R.P, R.σ g x = y ∧ θP y = sC g (θP x)
  galois_t_transform : ∀ g : K.fixingSubgroup, ∃ u : R.P, R.σ g R.tB = u * R.tB ∧ θP u = c g
  eσ : ∀ g x, e (sΛ g x) = R.σA g (e x)
  cris : ∀ g n x, sn g n (Y.c n x) = Y.c n (sΛ g x)

variable {R : Per l K} {Y : CB l K} {e : Y.Λ →+* R.A} {θP : R.P →+* ℂ_[l]} {sΛ : K.fixingSubgroup → Y.Λ →+* Y.Λ}
  {sn : K.fixingSubgroup → ∀ n, Y.R n →+* Y.R n} {sC : K.fixingSubgroup → ℂ_[l] →+* ℂ_[l]} {c : K.fixingSubgroup → ℂ_[l]}
  (hb : Br R Y e θP sΛ sn sC c) {m : ℕ} {L : Lev R m} (hL : L.Good)

include hb hL

theorem Br.θ_ex : ∃ θ : L.B →+* ℂ_[l], ∀ x, θ (L.toB x) = θP x := by
  refine ⟨(L.toB.liftOfSurjective hL.toB_surj) ⟨θP, fun x hx => ?_⟩, fun x => RingHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
  obtain ⟨y, hy⟩ := (hL.toB_ker x).1 hx
  obtain ⟨t, ht, -⟩ := hb.θ_i Y.t
  rw [hb.et] at ht
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hL.pos
  refine (hb.ker x).2 ⟨t ^ k * y, ?_⟩
  rw [hy, hk, pow_add, pow_one, Subring.coe_mul, SubmonoidClass.coe_pow, ht, mul_assoc]
  rfl

theorem Br.t_ex : ∃ t : R.P, (t : R.B) = R.tB ∧ L.ι (L.lam (e Y.t)) = L.toB t ∧ L.IB = Ideal.span {L.toB t} := by
  obtain ⟨t, ht, -⟩ := hb.θ_i Y.t
  refine ⟨t, by rw [ht, hb.et]; rfl, hL.ι_lam _ t ht, ?_⟩
  rw [← dividedPowerFiltration_one L.γB, hL.pdP_B 1 t (by rw [ht, hb.et]; rfl), pow_one]

def Br.θ : L.B →+* ℂ_[l] := (hb.θ_ex hL).choose

theorem Br.θ_toB (x : R.P) : hb.θ hL (L.toB x) = θP x := (hb.θ_ex hL).choose_spec x

theorem Br.ker_θ : RingHom.ker (hb.θ hL) = L.IB := by
  obtain ⟨t, ht, -, hI⟩ := hb.t_ex hL
  ext b
  obtain ⟨x, rfl⟩ := hL.toB_surj b
  rw [RingHom.mem_ker, hb.θ_toB, hI, Ideal.mem_span_singleton']
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (hb.ker x).1 h
    refine ⟨L.toB y, ?_⟩
    rw [← map_mul]
    exact congrArg L.toB (Subtype.ext (by rw [hy, Subring.coe_mul, ht, mul_comm]))
  · rintro ⟨a, ha⟩
    have h0 : θP t = 0 := (hb.ker t).2 ⟨1, by rw [ht]; simp⟩
    rw [← hb.θ_toB hL, ← ha, map_mul, hb.θ_toB, h0, mul_zero]

theorem Br.gr (i : ℕ) (hi : i < m) (x : L.B)
    (h : x * L.ι (L.lam (e Y.t)) ^ i ∈ Ideal.span {L.ι (L.lam (e Y.t)) ^ (i + 1)}) : x ∈ L.IB := by
  obtain ⟨t, ht, h1, hI⟩ := hb.t_ex hL
  rw [h1] at h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨x, rfl⟩ := hL.toB_surj x
  obtain ⟨a, rfl⟩ := hL.toB_surj a
  have h2 : L.toB (x * t ^ i - a * t ^ (i + 1)) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, map_pow, ha, sub_self]
  obtain ⟨y, hy⟩ := (hL.toB_ker _).1 h2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have h3 : x = (a + t ^ k * y) * t := by
    refine Subtype.ext (mul_right_cancel₀ (pow_ne_zero i hb.t_ne) ?_)
    push_cast at hy ⊢
    rw [ht] at hy ⊢
    linear_combination hy
  rw [hI, h3, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

def Br.lv (hd : ∀ n, ∃ d : RedIn (O := OK l K) (Y.γ n) (Y.κ n) L.γ l n, ∀ x, d.ρ (Y.c n x) = Ideal.Quotient.mk _ (L.lam (e x))) :
    Lv Y m where
  B := L.B
  IB := L.IB
  γB := L.γB
  θ := hb.θ hL
  A := L.A
  I := L.I
  γ := L.γ
  ι := L.ι
  lam := L.lam.comp e
  d n := (hd n).choose
  d_lam n := (hd n).choose_spec
  lat := hL.lat m le_rfl
  ι_dp := hL.ι_dp
  ι_O := hL.ι_O
  t_mem := by
    obtain ⟨t, -, h1, hI⟩ := hb.t_ex hL
    rw [hL.ι_I, Ideal.mem_comap, RingHom.comp_apply, h1, hI]
    exact Ideal.mem_span_singleton_self _
  θ_K k := by
    obtain ⟨y, h1, h2⟩ := hb.θ_o k
    rw [← hL.toB_K k y h1, hb.θ_toB, h2]
  θ_lam x := by
    obtain ⟨y, h1, h2⟩ := hb.θ_i x
    rw [RingHom.comp_apply, hL.ι_lam _ y h1, hb.θ_toB, h2]
  ker_θ := hb.ker_θ hL
  pdB r := by
    obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
    rw [RingHom.comp_apply, h1, hL.pdP_B r t ht]
  nil := by
    obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
    rw [RingHom.comp_apply, h1, ← map_pow]
    exact (hL.toB_ker _).2 ⟨1, by simp [ht]⟩
  gr := hb.gr hL

theorem Br.gal (hd) (g : K.fixingSubgroup) : Nonempty (LHom (hb.lv hL hd) (hb.lv hL hd) (sΛ g) (sn g) (sC g) (c g)) := by
  obtain ⟨u, hu, hc⟩ := hb.galois_t_transform g
  obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
  exact ⟨{
    le := le_rfl
    sA := L.σA g
    sB := L.σB g
    dpA := hL.σ_dp g
    dpB := hL.σB_dp g
    oA := hL.σ_O g
    oB := hL.σB_K g
    ι := fun a => (hL.σ_ι g a).symm
    lam := fun x => (hL.σ_lam g (e x)).trans (congrArg L.lam (hb.eσ g x).symm)
    cris := hb.cris g
    θ := fun b => by
      obtain ⟨x, rfl⟩ := hL.toB_surj b
      obtain ⟨y, h2, h3⟩ := hb.θ_σ g x
      change hb.θ hL (L.σB g (L.toB x)) = sC g (hb.θ hL (L.toB x))
      rw [hL.σB_toB g x y h2, hb.θ_toB, hb.θ_toB, h3]
    cB := L.toB u
    t := by
      change L.σB g (L.ι (L.lam (e Y.t))) = L.toB u * L.ι (L.lam (e Y.t))
      rw [h1, ← map_mul]
      exact hL.σB_toB g t (u * t) (by rw [Subring.coe_mul, ht, hu])
    θc := (hb.θ_toB hL u).trans hc }⟩

omit hL in
theorem Br.sys (S : LevSys R) (hS : S.Good)
    (hd : ∀ m n, ∃ d : RedIn (O := OK l K) (Y.γ n) (Y.κ n) (S.L m).γ l n,
      ∀ x, d.ρ (Y.c n x) = Ideal.Quotient.mk _ ((S.L m).lam (e x))) : Nonempty (LvSys Y sΛ sn sC c) :=
  ⟨{ L := fun m => hb.lv (hS.lev m) (hd m)
     dn := fun m =>
      { le := Nat.le_succ _
        sA := S.dA m
        sB := S.dB m
        dpA := hS.ddp m
        dpB := hS.ddpB m
        oA := hS.dO m
        oB := hS.dK m
        ι := hS.dι m
        lam := fun x => hS.dlam m (e x)
        cris := fun _ _ => rfl
        θ := fun b => by
          obtain ⟨x, rfl⟩ := (hS.lev (m + 1)).toB_surj b
          change hb.θ (hS.lev m) (S.dB m ((S.L (m + 1)).toB x)) = hb.θ (hS.lev (m + 1)) ((S.L (m + 1)).toB x)
          rw [hS.dB_toB, hb.θ_toB, hb.θ_toB]
        cB := 1
        t := by
          change S.dB m ((S.L (m + 1)).ι ((S.L (m + 1)).lam (e Y.t))) = 1 * (S.L m).ι ((S.L m).lam (e Y.t))
          rw [hS.dι, hS.dlam, one_mul]
        θc := map_one _ }
     gal := fun m g => (hb.gal (hS.lev m) (hd m) g).some }⟩

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.LatLink
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Pb.Lat

theorem dp_of_char {K A B A' B' : Type} [Field K] [CharZero K] [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra K B']
    {I : Ideal A} {I' : Ideal A'} {J : Ideal B} {J' : Ideal B'} (δ : DividedPowers J) (δ' : DividedPowers J') (ι : A →+* B)
    (ι' : A' →+* B') (s : A →+* A') (g : B →+* B') (hJ : J = I.map ι) (hJ' : J' = I'.map ι') (hs : I.map s ≤ I')
    (h : ∀ a, g (ι a) = ι' (s a)) : IsDPMorphism δ δ' g := by
  have h1 : J.map g ≤ J' := by
    rw [hJ, hJ', Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    change g (ι a) ∈ I'.map ι'
    rw [h]
    exact Ideal.mem_map_of_mem _ (hs (Ideal.mem_map_of_mem _ ha))
  refine ⟨h1, fun {n} a ha => ?_⟩
  have hu : IsUnit (n.factorial : B') := by
    have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 n.factorial_ne_zero) : IsUnit (n.factorial : K)).map (algebraMap K B')
    rwa [map_natCast] at this
  refine hu.mul_left_cancel ?_
  rw [δ'.factorial_mul_dpow_eq_pow (h1 (Ideal.mem_map_of_mem _ ha)), ← map_natCast g, ← map_mul, δ.factorial_mul_dpow_eq_pow ha, map_pow]

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem levHyp_ex [FiniteDimensional ℚ_[l] K] : ∃ M : ℕ, LevHyp l K M :=
  (_root_.GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub l K).imp fun M h => ⟨h, GlobalTheory.T.acris_mem_lattice_sub l M, _root_.GlobalTheory.CompanionTheory.LatCHc.hc_k l M, _root_.GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap l K,
    fun k g => _root_.GlobalTheory.CompanionTheory.LatGal.gal_mem_sub l K M k g _, _root_.GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub l M⟩

theorem lev_σ_ι (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) (a : (lev h k).A) :
    (lev h k).ι ((lev h k).σA g a) = (lev h k).σB g ((lev h k).ι a) :=
  ι_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) a

theorem lev_good (h : LevHyp l K M) (k : ℕ) (hk : 1 ≤ k) : (lev h k).Good := by
  exact {
    pos := hk
    lat := _root_.GlobalTheory.CompanionTheory.LatCBase.latBase_lev h k hk
    toB_surj := _root_.GlobalTheory.CompanionTheory.LatLevels.toB_surjective h k
    toB_ker := _root_.GlobalTheory.CompanionTheory.LatC.lev_toB_ker h k
    toB_K := _root_.GlobalTheory.CompanionTheory.LatC.toB_on_K h k
    ι_inj := ι_injective (fk l k) (xi0 l) l M
    ι_dp := dp_ι (fk l k) (xi0 l) l M (h.hc k)
    ι_I := rfl
    IB_eq := _root_.GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map h k
    ι_O := _root_.GlobalTheory.CompanionTheory.LatC.iota_algebraMap_OK h k
    ι_lam := _root_.GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB h k
    σB_toB := _root_.GlobalTheory.CompanionTheory.LatC.sigmaB_toB h k
    σ_ι := lev_σ_ι h k
    σ_lam := _root_.GlobalTheory.CompanionTheory.LatCSig.sig_lam h k
    σ_O := _root_.GlobalTheory.CompanionTheory.LatC.sigA_fix h k
    σ_dp := GlobalTheory.T.level_galois_isDPMorphism h k
    σB_dp g := dp_of_char (K := K) (lev h k).γB (lev h k).γB (lev h k).ι (lev h k).ι ((lev h k).σA g) ((lev h k).σB g)
      (_root_.GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map h k) (_root_.GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map h k) (GlobalTheory.T.level_galois_isDPMorphism h k g).1 fun a => (lev_σ_ι h k g a).symm
    σB_K := _root_.GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K h k
    pdP_B := _root_.GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow h k
  }

theorem dk_pk (k : ℕ) (x : BdRp l) : dk l k (pk l (k + 1) x) = pk l k x := rfl

theorem sys_dι (h : LevHyp l K M) (m : ℕ) (a : ((levSys h).L (m + 1)).A) :
    (levSys h).dB m (((levSys h).L (m + 1)).ι a) = ((levSys h).L m).ι ((levSys h).dA m a) :=
  (ι_map (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1)) (h.dIn (m + 1)) a).symm

theorem levSys_good (h : LevHyp l K M) : (levSys h).Good := by
  exact {
    lev m := lev_good h (m + 1) (Nat.le_add_left 1 m)
    dB_toB m x := dk_pk (m + 1) (pInv l x)
    dι := sys_dι h
    dlam m c := Subtype.ext (dk_pk (m + 1) (ACris.iota ℂ_[l] l c))
    dO m a := Subtype.ext (dk_pk (m + 1) (kP l K a))
    dK m k := dk_pk (m + 1) (kP l K k)
    ddp := GlobalTheory.T.level_system_transition_isDPMorphism h
    ddpB m := dp_of_char (K := K) ((levSys h).L (m + 1)).γB ((levSys h).L m).γB ((levSys h).L (m + 1)).ι ((levSys h).L m).ι
      ((levSys h).dA m) ((levSys h).dB m) (_root_.GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map h (m + 2)) (_root_.GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map h (m + 1)) (GlobalTheory.T.level_system_transition_isDPMorphism h m).1 (sys_dι h m)
    dσ := GlobalTheory.T.level_system_transition_galois_A h
    dσB := _root_.GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB h
    cpl := _root_.GlobalTheory.CompanionTheory.LatC.levSys_existsUnique h
  }

theorem levSys_ex [FiniteDimensional ℚ_[l] K] : ∃ S : Kap.LevSys (per l K), S.Good ∧ ∀ m, (S.L m).CrisOK :=
  (levHyp_ex (l := l) (K := K)).elim fun _ h => ⟨levSys h, levSys_good h, fun m => GlobalTheory.T.level_xi_mem_ideal_and_theta_compat h (m + 1)⟩

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ResMIncl
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.HT

open Pb

section Gen
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

def resM (r r' : ℤ) : CH.Mor (sq (thFil L r) (thFil L r')) (sq (sFil Q r) (sFil Q r')) (RingHom.id b.R) where
  G := Q.ι
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem resM_all (h : ∀ T, Q T) (r r' : ℤ) (n : ℕ) : Function.Bijective ((resM Q r r').pull n) := by
  have e1 : Q.ι.EssSurj := ⟨fun T => ⟨⟨T, h T⟩, ⟨Iso.refl _⟩⟩⟩
  have e2 : Q.ι.IsEquivalence := {}
  have : (resM Q r r').G.IsLeftAdjoint := inferInstanceAs Q.ι.IsLeftAdjoint
  exact CrystallineSemistableComparison.P.adj_mor _ (fun _ => Function.bijective_id) n

variable {Q} in
theorem resM_incl {Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) (n : ℕ) (x : CH.H (sq (thFil L r) (thFil L r')) n) :
    (resM Q' r r').pull n x = ((incl h).sq (incl_fil h r) (incl_fil h r')).pull n ((resM Q r r').pull n x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => ?_))
  change (z.1 (s ⋙ Q'.ι) : sqM _ _ _) = ((incl h).sq (incl_fil h r) (incl_fil h r')).τ _ (z.1 (s ⋙ Q'.ι))
  obtain ⟨y, hy, e⟩ := sq_surj _ _ (z.1 (s ⋙ Q'.ι))
  rw [← e]
  rfl

end Gen

section K
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def resH (Q : ObjectProperty (Thick (smFun X q))) (a n : ℕ) : Hdg q a n →ₗ[K] HQ Q (a : ℤ) ((a : ℤ) + 1) n :=
  (resM Q (a : ℤ) ((a : ℤ) + 1)).pull n

theorem res_bij (s : ℕ) (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (r r' : ℤ) (hr : r' ≤ s) (n : ℕ) :
    Function.Bijective ((resM (TO q 1 s 𝒱) r r').pull n) := by
  let Q₀ : ObjectProperty (Thick (smFun X q)) :=
    St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ {⊤}
  have h0 : ∀ T, Q₀ T := fun T => ⟨trivial, ⊤, rfl, le_rfl⟩
  have h1 : TO q 1 s {⊤} ≤ Q₀ := fun T _ => h0 T
  have h2 : TO q 1 s 𝒱 ≤ TO q 1 s {⊤} := fun T hT => ⟨hT.1, ⊤, rfl, le_rfl⟩
  have b0 := resM_all Q₀ h0 r r' n
  have b1 := refl (γ := dividedPowersBot K) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ 1 s (Or.inl ⟨rfl, rfl⟩) {⊤} h1 r r' hr n
  have b2 := (zar (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) 𝒱 {⊤} h2
    (fun W _ => by rw [h𝒱]; exact le_top) n).1 r r'
  have e : ⇑((resM (TO q 1 s 𝒱) r r').pull n) = ((incl h2).sq (incl_fil h2 r) (incl_fil h2 r')).pull n ∘
      ((incl h1).sq (incl_fil h1 r) (incl_fil h1 r')).pull n ∘ (resM Q₀ r r').pull n := funext fun x =>
    (resM_incl h2 r r' n x).trans (congrArg _ (resM_incl h1 r r' n x))
  rw [e]
  exact b2.comp (b1.comp b0)

theorem hdg_res (s : ℕ) (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (a : ℕ) (ha : a < s) (n : ℕ) :
    Function.Bijective (resH q (TO q 1 s 𝒱) a n) := res_bij q s 𝒱 h𝒱 _ _ (by omega) n

end K

end CrystallineSemistableComparison.HT
end
end

