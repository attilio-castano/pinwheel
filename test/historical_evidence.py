"""Opt-in replay of local historical evidence, separate from portable controls.

Enabling replay never suppresses missing/corrupt evidence: the decorated test
runs normally and must authenticate its inputs. Default discovery reports the
unexecuted replay checks explicitly as skips, without an acceptance claim.
"""
import os
import unittest


ENVIRONMENT = 'PINWHEEL_RUN_HISTORICAL_TESTS'


def historical_evidence(test):
    return unittest.skipUnless(
        os.environ.get(ENVIRONMENT) == '1',
        'Historical evidence replay not requested; set ' + ENVIRONMENT + '=1',
    )(test)
