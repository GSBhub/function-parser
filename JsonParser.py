#!/usr/bin/python

import sys
import json
import xlsxwriter
import r2pipe
import xlrd
from func_finder import _get_start, _get_rst
from collections import OrderedDict

# Predefined functions containing sensor addresses for comparision's
sensors = {
    'batt_voltage': ['0x9a56', '0x9f5b', '0xa166', '0xa307', '0xae2c', '0xd982', '0xe1cd'],
    'vehicle_speed': ['0x9be8', '0x9dce', '0xa59d', '0xa9a7', '0xafc6', '0xb960'],
    'engine_speed': ['0xa59d', '0xa5ec', '0xa9a7', '0xafc6', '0xb5bf', '0xb960'],
    'water_temp': ['0x9b46', '0xab56'],
    'ignition_timing': ['0xdb1a', '0xda0f'],
    'airflow': ['0xddcd'],
    'throttle_position': ['0xe1cd'],
    'knock_correction': ['0xafc6']
}
# How far left & right to show address range
hex_margin = 250

class EcuFile:
    def __init__(self, file_name, functions, gt=None):
        """
        EcuFile constructor
        :param file_name: File name of ECU binary
        :param functions: JSON of function address & block hashes
        """
        self.functions = OrderedDict()

        split = file_name.split('/')
        self.file_name = split[len(split) - 1]
        name = self.file_name.split('-')
        self.name = name[0][4:] + '-' + name[1][2:] + '-' + name[4].split('.')[0]
        
        local_gt = dict(gt)

        r2 = r2pipe.open('./bins/' + self.file_name, ["-2"])
        start = _get_start(file_name) # using private functions here, but oh well
        rst = _get_rst(r2)
        r2.cmd('e asm.arch=m7700')
        r2.cmd('e anal.limits=true')
        r2.cmd('e anal.from={}'.format(start if rst > start else rst))
        r2.cmd('e anal.to=0xfffe')
        r2.cmd('s {}'.format(rst))
        r2.cmd('aaa') # analyze all

        for address, hashes in functions.items():
            # Clean up hashes
            hashes = hashes[1:-1].split(',')
            hashes = [x.replace('\'', '') for x in hashes]
            hashes = [x.strip(' ') for x in hashes]

            if hashes != [''] and int(address, 16) > 36864:
                    self.functions[address] = hashes

        if self.name in local_gt.keys():
            for sensor_type, l in dict(local_gt[self.name]).iteritems():
                for addr in list(l):
                    r2.cmd("s {}".format(addr)) # seek to addr from XLSX
                    r2.cmd("sf.") # seek to beginning of function
                    gt[self.name][sensor_type][ # change addrs from file to point to start of function
                        gt[self.name][sensor_type].index(addr)] = r2.cmd("s") 
        r2.quit()
        print('Created ECU file ' + self.file_name)

class Cell:
    
    def __init__(self, func_addr, jaccard, flags=None):
        self.func_addr = func_addr
        self.jaccard = jaccard
        if flags is not None:
            self.flags = flags
        else:
            self.flags = { # more can be added in the future
        'Guess_Candidate' : False, # is a guess candidate (mark yellow)
        'Max_Row': False,          # is highest jaccard value
        'Control_Value': False     # matches control address  
        }
        self.row = None
        self.col = None

class IndexTable:

    def __init__(self, ecu_file_1, ecu_file_2):
        """
        IndexTable constructor
        :param ecu_file_1, ecu_file_2: ECU files used for this table
        """
        self.indexes = OrderedDict()
        self.tables = OrderedDict()
        
        self.name = ecu_file_1.name + ' ' + ecu_file_2.name
        self.test_name = ecu_file_2.file_name

        # Custom cell formats
        self.header_format = book.add_format({'font_color': 'white', 'bg_color': 'black'})
        self.purple_format = book.add_format({'font_color': 'white', 'bg_color': 'purple'})
        self.blue_format = book.add_format({'font_color': 'white', 'bg_color': 'blue'})
        self.yellow_format = book.add_format({'font_color': 'black', 'bg_color': 'yellow'})
        self.red_format = book.add_format({'font_color': 'white', 'bg_color': 'red'})

        print('Created index table ' + self.name)

    def push_index(self, function_1, function_2, jaccard_index):
        """
        Adds new 'cell' for table
        :param function_1, function_2: Header addresses
        :param jaccard_index: Jaccard Index calculation
        """
        self.indexes[function_1, function_2] = Cell(function_2, jaccard_index)

    def _write_format(self, sheet, highest_index, sensor_addr):
        """
        Format cells with result data
        :param sheet: Excel sheet to write write results
        :param highest_index: Highest jaccad index in row
        """

        if sensor_addr: 
            sheet.conditional_format(
                highest_index[0], highest_index[1], highest_index[0], highest_index[1],
                {'type': 'no_errors', 'format': self.purple_format}
            )  # match condition - color a match with man analysis purple
        else:
            sheet.conditional_format(
                highest_index[0], highest_index[1], highest_index[0], highest_index[1],
                {'type': 'no_errors', 'format': self.blue_format}
            ) # non-match - color it blue instead

    def write_results(self, book, gt):
        """
        Writes all results to Excel sheet
        :param book: Excel sheet containing result data
        :param test_blocks: Code blocks to test results with
        """
        print('Loading sheet ' + table.name)

        sheet = book.add_worksheet(table.name)
        sheet.freeze_panes(0, 1)
        sheet.set_column(0, 0, 23)

        global sensors

        row, col = 0, 0
        highest_index = [0, 0, 0]
        left_margin, right_margin = 0, 0
        tmp_key = ''
        addr_list = None
        sensor_addr = None        
        man_addrs = list()
        max_rows = {}

        sensor_name = table.name.split(" ")[1]
        if sensor_name in gt.keys(): # pull ID'd addr row of manual analysis data from table
            addr_list = gt[sensor_name] 

        # Write results to cells
        for keys, cell in table.indexes.items():
            # Switch to new row
            jaccard_index = cell.jaccard
            if keys[0] != tmp_key: # process first pos of new row
                tmp_key = keys[0]
                row = row + 1
                col = 1
                cell.row = row
                cell.col = col
                # Side header for each row
                sheet.write(row, 0, keys[0], self.header_format)
                print('\t Added row {}'.format(keys[0]))

                # Pull list of man analysis using keys
                if addr_list is not None:
                    if "batt_voltage" in tmp_key:
                        man_addrs = addr_list["Battery Voltage"]
                    elif "vehicle_speed" in tmp_key:
                        man_addrs = addr_list["Vehicle Speed"]
                    elif "engine_speed" in tmp_key:
                        man_addrs = addr_list["Engine Speed"]
                    elif "water_temp" in tmp_key:
                        man_addrs = addr_list["Water Temp."]
                    elif "ignition_timing" in tmp_key:
                        man_addrs = addr_list["Vehicle Speed"]
                    elif "airflow" in tmp_key:
                        man_addrs = addr_list["Airflow Sensor"]
                    elif "throttle_position" in tmp_key:
                        man_addrs = addr_list["Throttle Position Sensors"]
                    elif "knock_correction" in tmp_key:
                        man_addrs = addr_list["Knock Correction"]

                    ctrl_addr = keys[0][keys[0].find("(")+1:keys[0].find(")")]
                    test = sensors[ctrl_addr].index(keys[0][0:6])
                    sensor_addr = man_addrs[test]

                if highest_index != [0, 0, 0]:
                    max_rows[keys[0]] = cell
                highest_index = [0, 0, 0]

                # Set address range margins
                hex_addr = int(keys[0].split(' ')[0], 16)
                left_margin = hex_addr - hex_margin
                right_margin = hex_addr + hex_margin

            else:# process rest of row

                col = col + 1
                cell.row = row
                cell.col = col

                if len(man_addrs) is not 0:
                    ctrl_addr = keys[0][keys[0].find("(")+1:keys[0].find(")")]
                    test = sensors[ctrl_addr].index(keys[0][0:6])
                    sensor_addr = man_addrs[test]

            # Check if encountered higher Jaccard index
            if jaccard_index > highest_index[2]:
                highest_index = [row, col, jaccard_index]
                max_rows[keys[0]] = cell

            # read the sample graph and write everything to spreadsheet
            if (sensor_addr is not None) and (sensor_addr.rstrip() in keys[1]):
                cell.flags["Control_Value"] = True
                
            # Highlight "estimate" address margins
            if int(keys[1], 16) >= left_margin and int(keys[1], 16) <= right_margin:
                cell.flags["Guess_Candidate"] = True

            # write col headers (addresses)
            sheet.write(0, col, keys[1], self.header_format)

        # flag all of the "max" candidate items
        for _, cell in max_rows.iteritems():
            cell.flags["Max_Row"] = True

        # write all results to spreadsheet
        for _, cell in table.indexes.items():
            self._write_cells(sheet, cell, cell.row, cell.col, keys, round(cell.jaccard , 2))

    # Read the cell object, process the cells, write results to the sheet
    # Object flags determine what color to add
    # Add a new flag to the "flags" dict in the "cell" object if we need new
    # colors
    def _write_cells(self, sheet, cell, row, col, keys, jaccard_index):
        # write header for row

        # specify format for writing cell
        write_format = None
        if cell.flags["Max_Row"]:
            write_format = self.blue_format
            if cell.flags["Control_Value"]: 
                write_format = self.purple_format        
        elif cell.flags["Control_Value"]:
            write_format = self.red_format
        elif cell.flags["Guess_Candidate"]:
            write_format = self.yellow_format

        sheet.write(row, col, jaccard_index, write_format)

def _jaccard_index(list_1, list_2):
    """
    Calculate Jaccard index from two lists (Use shortest list as check)
    :param list_1, list_2: Lists to compare
    :returns: Jaccard index of list_1 & list_2
    """
    if len(list_1) < len(list_2):
        intersection = len([x for x in list_1 if x in list_2])
    else:
        intersection = len([x for x in list_2 if x in list_1])

    union = len(list_1) + len(list_2) - intersection

    return float(intersection) / union


def _create_tables(control_file, ecu_files):
    """
    Creates comparison tables
    :param ecu_files: List of EcuFile objects
    :returns: List of created tables
    """
    tables = []

    for ecu_file in ecu_files:
        table = IndexTable(control_file, ecu_file)

        # Loop through functions in ECU files
        for function_1, function_1_hashes in control_file.functions.items():
            for function_2, function_2_hashes in ecu_file.functions.items():
                for sensor, addresses in sensors.items():
                    if function_1 in addresses:
                        table.push_index(
                            function_1 + ' (' + sensor + ')',
                            function_2,
                            _jaccard_index(function_1_hashes, function_2_hashes)
                        )
                        break

        tables.append(table)

    return tables

# Process the ground truth/manual analysis data by loading it in
# This data is used to verify all of our nodes that are found using our
# automatic method
# Returns: Nested dictionary laid out as follows
# Binary name: Sensor name: [All sensor functions manually found]
# for each binary, sensor, and values in the provided file
def _process_gt(sheet):
    ret = dict()
    code_blocks = xlrd.open_workbook(sheet)
    gt = code_blocks.sheet_by_index(0) # pull man analysis ground truth
    i = 1
    bin_nms = dict()

    while i < 21: # we have 10 valid/working samples currently
        bin_nms[i] = gt.cell(0, i).value
        i += 2

    sensor_nms = gt.col_values(0, 2)

    for col, bin_nm in bin_nms.iteritems(): 
        sensor_addr = gt.col_values(col, 2) 
        code_block_addr = gt.col_values(col + 1, 2)

        tmp = {}
        for _ in range(0, 8):
            tmp[sensor_nms[_]] = code_block_addr[_].splitlines()

        ret[bin_nm] = tmp
    return ret

if __name__ == '__main__':
    ecu_files = []
    control_file = None
    gt = None 

    if len(sys.argv) < 3:
        print('Run \'python JsonParser.py file.json output.xlsx')
        exit()

    gt = _process_gt("code_blocks.xlsx")
    # Open & parse JSON dump
    with open(sys.argv[1]) as file:
        json_data = json.load(file, object_pairs_hook=OrderedDict)

        for file_name in json_data:
            ecu_file = EcuFile(file_name, json_data[file_name], gt)

            # Pick out control file
            if ecu_file.name == '27-93-EG33':
                control_file = ecu_file
            else:
                ecu_files.append(ecu_file)

    # Setup Excel sheet
    book = xlsxwriter.Workbook(sys.argv[2])
    tables = _create_tables(control_file, ecu_files)

    # Write all table data to sheets
    for table in tables:
        table.write_results(book, gt)
        # write GT data to sheets

    book.close()

    print('\nWrote values to {}\n'.format(sys.argv[2]))
    # print('Final results {}%\n'.format(round((float(results[0]) / results[1]) * 100), 2))
