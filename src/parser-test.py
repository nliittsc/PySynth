from lexer import lexer
from parser import parser

# test for lexer
if __name__ == '__main__':

    import glob
    for f in glob.glob("examples/*"):

        with open(f) as example:
            print("Processing Example File {}".format(f))

            fulltext = example.read()

            # print("-" * 10)
            # print("lexer")
            # print("-" * 10)

            lexer.input(fulltext)

            # Tokenize

            # while True:
            #     tok = lexer.token()
            #     if not tok: 
            #         break
            #     print(tok)


            print('parse result:')
            print("-" * 10)

            program = parser.parse(fulltext)
            print(program)
            print("-" * 10)


            

