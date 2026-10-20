"""Native checker report completeness and actual violation refusal controls."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_tt_layout import geometry_result

REPORT='''<report-database><top-cell>top</top-cell><categories>
<category><name>M1.a</name><categories/></category></categories>
<cells><cell><name>top</name></cell></cells><items>{items}</items></report-database>'''
ITEM="<item><category>'M1.a'</category><cell>top</cell><multiplicity>1</multiplicity></item>"


class NativeLayoutReportTests(unittest.TestCase):
    def test_actual_violations_reject_regardless_of_successful_process(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'native.xml';path.write_text(REPORT.format(items=ITEM))
            result=geometry_result(path,'top',expected_categories=[['M1.a']])
            self.assertFalse(result['passed']);self.assertEqual(result['violation_items'],1)
            path.write_text(REPORT.format(items=''))
            self.assertTrue(geometry_result(path,'top',expected_categories=[['M1.a']])['passed'])

    def test_empty_reordered_wrong_top_and_missing_checks_cannot_supply_acceptance(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'native.xml';base=REPORT.format(items='')
            for text,top,expected in [(base,'other',[['M1.a']]),(base,'top',[['M1.a'],['M2.a']]),
                (base.replace('<category><name>M1.a</name><categories/></category>',''),'top',[['M1.a']])]:
                path.write_text(text)
                with self.subTest(text=text,top=top),self.assertRaises(ValueError):geometry_result(path,top,expected_categories=expected)

    def test_unknown_category_cell_or_invalid_multiplicity_refuses(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'native.xml'
            for item in [ITEM.replace("'M1.a'","'M2.a'"),ITEM.replace('<cell>top</cell>','<cell>other</cell>'),
                ITEM.replace('<multiplicity>1</multiplicity>','<multiplicity>0</multiplicity>')]:
                path.write_text(REPORT.format(items=item))
                with self.subTest(item=item),self.assertRaises(ValueError):geometry_result(path,'top')


if __name__=='__main__':unittest.main()
