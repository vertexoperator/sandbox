#-*- coding:utf-8 -*-
"""
g94フォーマットの基底関数データを読み込む


基底関数セットは、例えば
EMSL Basis Set Exchange
https://bse.pnl.gov/bse/portal
で、様々なフォーマットで配布されている
"""
def readBasis_g94(fp):
    def float_g94(s):
        return float(s.replace('D' , 'e'))
    ret = {}
    atoms = [None , "H","He","Li","Be","B","C","N","O","F","Ne","Na","Mg","Al","Si","P","S","Cl","Ar",
             "K","Ca","Sc","Ti","V","Cr","Mn","Fe","Co","Ni","Cu","Zn","Ga","Ge","As","Se","Br","Kr"]
    lines = [line for line in fp if line[0]!='!' and len(line.strip())>0][1:]
    idx = 0
    while True:
        if idx==len(lines):break
        atomname = lines[idx].split()[0]
        assert(atomname in atoms),("未知の原子 %s" % atomname)
        atno = atoms.index(atomname)
        idx += 1
        ret[str(atno)] = []
        while True:
            ls = lines[idx].split()
            if len(ls)<2:
               idx+=1
               break
            orbtype = list(ls[0])
            contnum = int(ls[1])
            for c,orb in enumerate( orbtype ):
               ndata = []
               for i in xrange(contnum):
                  ls = lines[idx+i+1].split()
                  ndata.append( (float_g94(ls[0]) , float_g94(ls[c+1])) )
               ret[str(atno)].append( (orb , ndata) )
            idx+=(contnum+1)
    return ret



"""
pdbファイルから原子の座標データを読む
"""
def readpdb(filename):
   atoms = [None , "H","He","Li","Be","B","C","N","O","F","Ne",
            "Na","Mg","Al","Si","P","S","Cl","Ar",
            "K","Ca","Sc","Ti","V","Cr","Mn","Fe","Co","Ni","Cu","Zn",
            "Ga","Ge","As","Se","Br","Kr"]
   def angstrom2bohr(r):
      return float(r)*1.8897261249935898
   ret = []
   for line in open(filename):
      ls = line.strip().split()
      if len(ls)<7:continue
      if ls[0]!="ATOM":continue
      ret.append( (atoms.index(ls[2]) , angstrom2bohr(ls[4]) , angstrom2bohr(ls[5]) , angstrom2bohr(ls[6])) )
   return ret


