s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T38-[6,4,6]-611-44-332-g1";
s`BelyiDBFilename := "8T38-[6,4,6]-611-44-332-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 > |
[ 8, 2, 1, 3, 4, 6, 5, 7 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ],
[ 5, 8, 2, 7, 1, 4, 6, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 8, 2, 1, 3, 4, 6, 5, 7 ],
\[ 7, 4, 1, 6, 3, 8, 5, 2 ],
\[ 5, 8, 2, 7, 1, 4, 6, 3 ]:
 Order := 192 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 2, 1, 3, 4, 6, 5, 7 ],
\[ 7, 4, 1, 6, 3, 8, 5, 2 ],
\[ 5, 8, 2, 7, 1, 4, 6, 3 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 8, 2, 1, 3, 4, 6, 5, 7 ],
\[ 7, 4, 1, 6, 3, 8, 5, 2 ],
\[ 5, 8, 2, 7, 1, 4, 6, 3 ]:
 Order := 192 > |
[ 8, 2, 1, 3, 4, 6, 5, 7 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ],
[ 5, 8, 2, 7, 1, 4, 6, 3 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 > |
[ 8, 2, 1, 3, 4, 6, 5, 7 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ],
[ 5, 8, 2, 7, 1, 4, 6, 3 ]
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
