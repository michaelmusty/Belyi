s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T30-[12,12,3]-432-432-333-g1";
s`BelyiDBFilename := "9T30-[12,12,3]-432-432-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 12, 12, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 2, 1, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 648 > |
[ 6, 7, 5, 3, 4, 2, 1, 9, 8 ],
[ 9, 1, 6, 8, 7, 4, 5, 3, 2 ],
[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 6, 7, 5, 3, 4, 2, 1, 9, 8 ],
\[ 9, 1, 6, 8, 7, 4, 5, 3, 2 ],
\[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]:
 Order := 648 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 6, 7, 5, 3, 4, 2, 1, 9, 8 ],
\[ 9, 1, 6, 8, 7, 4, 5, 3, 2 ],
\[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]:
 Order := 648 >) |
[ PermutationGroup<9 |  
\[ 6, 7, 5, 3, 4, 2, 1, 9, 8 ],
\[ 9, 1, 6, 8, 7, 4, 5, 3, 2 ],
\[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]:
 Order := 648 > |
[ 6, 7, 5, 3, 4, 2, 1, 9, 8 ],
[ 4, 3, 9, 1, 2, 8, 6, 7, 5 ],
[ 8, 7, 1, 9, 2, 4, 5, 3, 6 ]
],
[ PermutationGroup<9 |  
\[ 6, 7, 5, 3, 4, 2, 1, 9, 8 ],
\[ 9, 1, 6, 8, 7, 4, 5, 3, 2 ],
\[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]:
 Order := 648 > |
[ 6, 7, 5, 3, 4, 2, 1, 9, 8 ],
[ 2, 9, 6, 8, 7, 5, 3, 4, 1 ],
[ 5, 3, 8, 6, 7, 9, 1, 2, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 2, 1, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 648 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 2, 1, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 648 > |
[ 6, 7, 5, 3, 4, 2, 1, 9, 8 ],
[ 9, 1, 6, 8, 7, 4, 5, 3, 2 ],
[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 2, 1, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 648 > |
[ 7, 8, 5, 3, 4, 9, 2, 1, 6 ],
[ 2, 9, 7, 6, 8, 4, 5, 3, 1 ],
[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
