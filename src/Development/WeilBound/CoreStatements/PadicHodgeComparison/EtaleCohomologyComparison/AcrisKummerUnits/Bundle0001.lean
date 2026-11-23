module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0159
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0161
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0160
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicComplete
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0163
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0170
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0177
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0165
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0164
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0174
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0169
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0173
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0178
public import GroundTheory.PAdicHodge.TiltAlgClosed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0185
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0190
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0168
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0179
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0162

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.AcrisModLBaseChange
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem CrystallineSemistableComparison.RL.d_ob : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := _root_.GlobalTheory.CompanionTheory.TiltFacts.obFacts

theorem CrystallineSemistableComparison.RL.acris_mod_l_base_change : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcr1 l := GlobalTheory.T.acris_level_one_facts

theorem CrystallineSemistableComparison.RL.d_seq : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcrSeq l := _root_.GlobalTheory.CompanionTheory.LSeq.racrSeq
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.FiltrationSpanDividedPowers
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem CrystallineSemistableComparison.RL.u_tf : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), (l : A.U) ∈ nonZeroDivisors A.U ∧ A.xi ∈ nonZeroDivisors A.W ∧ ∀ (n : ℕ) (x : A.W), A.xi * x ∈ Ideal.span {(l : A.W) ^ n} → x ∈ Ideal.span {(l : A.W) ^ n} := _root_.GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular

theorem CrystallineSemistableComparison.RL.u_mod : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.aToU1 ∧ RingHom.ker A.aToU1 = Ideal.span {A.pi} := _root_.GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker

theorem CrystallineSemistableComparison.RL.u_complete : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsAdicComplete (Ideal.span {(l : A.U)}) A.U := _root_.GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U

theorem CrystallineSemistableComparison.RL.sharp_cong : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), (∀ (a b : A.A) (n : ℕ), a - b ∈ Ideal.span {A.pi} → A.sharp (a ^ l ^ n) - A.sharp (b ^ l ^ n) ∈ Ideal.span {(l : A.U) ^ (n + 1)}) ∧ (∀ a b : A.A, A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi}) ∧ ∀ e : A.A, IsIdempotentElem e → A.sharp (1 - e) = 1 - A.sharp e := _root_.GlobalTheory.CompanionTheory.Untilt.sharp_congruences

theorem CrystallineSemistableComparison.RL.tilt_ex : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (u : ℕ → A.U), (∀ i, u (i + 1) ^ l = u i) → ∃ a : ℕ → A.A, (∀ i, a (i + 1) ^ l = a i) ∧ ∀ i, A.sharp (a i) = u i := _root_.GlobalTheory.CompanionTheory.Untilt.exists_compatible_roots_of_sharp

theorem CrystallineSemistableComparison.RL.tilt_inj : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : ℕ → A.A), (∀ i, a (i + 1) ^ l = a i) → (∀ i, b (i + 1) ^ l = b i) → (∀ i, A.sharp (a i) = A.sharp (b i)) → a = b := GlobalTheory.T.tilt_sequence_determined_by_sharp

theorem CrystallineSemistableComparison.RL.filtration_multiplicative : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.Fil0 0 = ⊤ ∧ (∀ i j, A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j)) ∧ (∀ k, (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k) ∧ (∀ r s, A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s)) ∧ (∀ n r, A.Fil n r = (A.Fil0 r).map (A.mkAcr n)) ∧ (∀ n, A.PFil n = A.PFil0.map (A.mkAcr n)) ∧ (∀ n, A.Fil n 0 = ⊤) ∧ ∀ n r s, A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) := _root_.GlobalTheory.CompanionTheory.FilMul.main

theorem CrystallineSemistableComparison.RL.gr : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n r : ℕ), (∀ z ∈ A.Fil n r, ∃ w : A.W, z - A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1)) ∧ ∀ w : A.W, A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1) ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := _root_.GlobalTheory.CompanionTheory.PerfFil.graded_mod_pow

theorem CrystallineSemistableComparison.RL.uToQ : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (A.uToQ n) ∧ RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} ∧ Function.Surjective (A.uToPQ n) ∧ (n ≠ 0 → RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)}) := _root_.GlobalTheory.CompanionTheory.Untilt.uToQ_main

theorem CrystallineSemistableComparison.RL.expand_nat : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (B : PAlg l) (f : A ⟶ B), (∀ a, mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a)) ∧ (∀ c : ℕ →₀ A.A, mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _))) ∧ (∀ a, mapU f (A.sharp a) = B.sharp (Hom.f f a)) ∧ (∀ a, mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a)) ∧ (∀ n x, Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x))) ∧ ∀ x : Ainf l, algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) := _root_.GlobalTheory.CompanionTheory.PAlgNat.expand_nat

theorem CrystallineSemistableComparison.RL.pdi : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.PdI (A.Fil0 1) ∧ R.PdI A.PFil0 ∧ ∀ x ∈ A.Fil0 1, ∀ (k : ℕ) (y : A.Acr0), (k.factorial : A.Acr0) * y = x ^ k → y ∈ A.Fil0 k := _root_.GlobalTheory.CompanionTheory.PerfFil.pdI_main

theorem CrystallineSemistableComparison.RL.pd_ex : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ δ : DividedPowers (A.Fil n 1), R.IsPd (A.mkAcr n) (A.Fil0 1) δ) ∧ ∃ δ : DividedPowers (A.PFil n), R.IsPd (A.mkAcr n) A.PFil0 δ := _root_.GlobalTheory.CompanionTheory.PerfFil.exists_dividedPowers_fil_pfil

theorem CrystallineSemistableComparison.RL.theta_ex : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), ∃ θ : A.Acr n →+* A.Un n, (∀ x : A.W, θ (A.toAcr n x) = Ideal.Quotient.mk _ (A.th x)) ∧ RingHom.ker θ = A.Fil n 1 := _root_.GlobalTheory.CompanionTheory.PerfectAlg.exists_theta_mod

theorem CrystallineSemistableComparison.RL.base_ex : ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {pFlat l}) (Ob l) ∧ pFlat l ∈ nonZeroDivisors (Ob l) := _root_.GlobalTheory.CompanionTheory.TiltCompl.complete_tf

theorem CrystallineSemistableComparison.RL.base_acr : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsBase l A → (Function.Bijective A.cris0 ∧ Function.Bijective A.oC) ∧ ∀ n, Function.Surjective (A.cris n) ∧ RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} := _root_.GlobalTheory.CompanionTheory.BaseAcris.main

theorem CrystallineSemistableComparison.RL.tens : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _)) ∧ ∀ z : TensorProduct (Ainf l) (Acris l) A.W, Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _) z = 0 ↔ z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n} := _root_.GlobalTheory.CompanionTheory.PerfFil.tens_base_change

theorem CrystallineSemistableComparison.RL.untilt_valuation_mod_square : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest → ∃ ϖ : A.U, ϖ ^ l = (l : A.U) ∧ R.Val0 (A.U ⧸ Ideal.span {ϖ ^ 2}) ∧ R.Aic (A.U ⧸ Ideal.span {ϖ ^ 2}) := _root_.GlobalTheory.CompanionTheory.Untilt.untilt_mod_varpi_sq

theorem CrystallineSemistableComparison.RL.idem_au : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.U), IsIdempotentElem e → ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e := GlobalTheory.T.existsUnique_idempotent_lift_tilt

theorem CrystallineSemistableComparison.RL.unit_lift : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : A.A), IsUnit (A.sharp a) → IsUnit a := GlobalTheory.T.isUnit_of_isUnit_sharp'

theorem CrystallineSemistableComparison.RL.mu_lc : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.Val (l : A.U) → ∀ (n : ℕ) (ζ : OC l), IsPrimitiveRoot ζ (l ^ n) → ∀ z : A.U, z ^ l ^ n = 1 → ∃ e : ZMod (l ^ n) → A.A, (haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩; CompleteOrthogonalIdempotents e) ∧ ∀ c, A.sharp (e c) * (z - A.oC ζ ^ c.val) = 0 := GlobalTheory.T.idempotents_of_prime_power_root_of_unity

theorem CrystallineSemistableComparison.RL.cont_ex : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (Γ : Type) [TopologicalSpace Γ], PerfectRing (A.contR Γ) l ∧ IsAdicComplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) ∧ A.contC Γ A.pi ∈ nonZeroDivisors (A.contR Γ) ∧ ∀ (k : ℕ) (f : A.contR Γ), f ∈ Ideal.span {A.contC Γ A.pi ^ k} ↔ ∀ γ, f.1 γ ∈ Ideal.span {A.pi ^ k} := _root_.GlobalTheory.CompanionTheory.ContFn.main

theorem CrystallineSemistableComparison.RL.tw_fil : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)), (∀ x ∈ (tw σ A).Fil0 1, (pdOk_twId σ A).acr0 x ∈ A.Fil0 1) ∧ (∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)}) ∧ (∀ n r, ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r) ∧ (∀ n, Function.Bijective (twAcr σ A n)) ∧ ∀ n x, twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) := _root_.GlobalTheory.CompanionTheory.TwFil.tw_fil
end

