"""Missing wire models and changed units/layers cannot become qualified timing."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_tt_rc import validate_nominal_rc


class NominalRCTests(unittest.TestCase):
    def test_actual_lef_units_and_missing_zero_or_changed_rc_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'tech.lef'
            source='\n'.join('LAYER '+name+'\n  TYPE ROUTING ;\n  WIDTH 0.2 ;\n  RESISTANCE RPERSQ 0.1 ;\n  CAPACITANCE CPERSQDIST 0.00003 ;\n  EDGECAPACITANCE 0.00004 ;\nEND '+name for name in ('Metal1','Metal2','Metal3','Metal4','TopMetal1'))
            path.write_text(source)
            config=dict(RT_MAX_LAYER='Metal4',LAYERS_RC={'nom_*':{name:dict(res=0.0005,cap=0.000086)
                for name in ('Metal1','Metal2','Metal3','Metal4','TopMetal1')}})
            result=validate_nominal_rc(config,path)
            self.assertFalse(result['extracted']);self.assertFalse(result['min_max_rc_qualified'])
            for bad in ({}, {'nom_*':{}}, {'nom_*':{name:dict(res=0,cap=0) for name in config['LAYERS_RC']['nom_*']}}):
                with self.assertRaisesRegex(ValueError,'differs'):validate_nominal_rc(dict(config,LAYERS_RC=bad),path)
            with self.assertRaisesRegex(ValueError,'Metal4'):validate_nominal_rc(dict(config,RT_MAX_LAYER='TopMetal1'),path)
            for bad in (source.replace('RPERSQ 0.1','RPERSQ 0'),source.replace('EDGECAPACITANCE 0.00004','EDGECAPACITANCE NaN'),source.replace('WIDTH 0.2','WIDTH 0')):
                path.write_text(bad)
                with self.assertRaises((ValueError,ArithmeticError)):validate_nominal_rc(config,path)


if __name__=='__main__':unittest.main()
